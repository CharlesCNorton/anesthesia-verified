(******************************************************************************)
(*                                                                            *)
(*                         Anesthesia Dosing Rules                            *)
(*                                                                            *)
(*     Propofol and fentanyl induction/maintenance dosing by weight, age,     *)
(*     and ASA class. Models the therapeutic window between awareness and     *)
(*     respiratory depression.                                                *)
(*                                                                            *)
(*     Gentlemen, this is no humbug.                                          *)
(*     (John Collins Warren, Massachusetts General Hospital, 1846)            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: PATIENT CLASSIFICATION                                          *)
(******************************************************************************)

(* ASA Physical Status Classification (ASA I-VI) *)
Inductive ASAClass : Type :=
  | ASA_I    (* normal healthy patient *)
  | ASA_II   (* mild systemic disease *)
  | ASA_III  (* severe systemic disease *)
  | ASA_IV   (* severe disease, constant threat to life *)
  | ASA_V    (* moribund; not expected to survive without operation *)
  | ASA_VI.  (* brain-dead; organ donation *)

(* Age categories relevant to dosing adjustments *)
Inductive AgeGroup : Type :=
  | Pediatric    (* < 12 years *)
  | Adult        (* 12-64 years *)
  | Elderly.     (* >= 65 years *)

(* Airway classification (Mallampati) *)
Inductive MallampatiClass : Type :=
  | Mallampati_I    (* full visibility of soft palate *)
  | Mallampati_II   (* soft palate, fauces, uvula visible *)
  | Mallampati_III  (* soft palate, base of uvula visible *)
  | Mallampati_IV.  (* only hard palate visible — difficult airway *)

Definition difficult_airway (m : MallampatiClass) : bool :=
  match m with
  | Mallampati_III => true
  | Mallampati_IV  => true
  | _              => false
  end.

(******************************************************************************)
(* SECTION 2: DOSE UNITS (integer micro-fractions)                           *)
(******************************************************************************)

(* We represent doses as integers scaled by 100 to avoid real arithmetic.
   E.g., 1_50 means 1.50 mg/kg (stored as 150).
   All comparisons use these scaled integers. *)

(* Propofol induction dose range by ASA/age (mg/kg x100):
   Standard adult:       100-250  (1.0-2.5 mg/kg)
   Elderly / ASA III-IV:  50-150  (0.5-1.5 mg/kg)
   Pediatric:            250-350  (2.5-3.5 mg/kg) *)

Definition propofol_induction_lo (asa : ASAClass) (age : AgeGroup) : nat :=
  match age with
  | Pediatric => 250
  | Elderly   => 50
  | Adult     =>
      match asa with
      | ASA_I | ASA_II => 100
      | _              => 50
      end
  end.

Definition propofol_induction_hi (asa : ASAClass) (age : AgeGroup) : nat :=
  match age with
  | Pediatric => 350
  | Elderly   => 150
  | Adult     =>
      match asa with
      | ASA_I | ASA_II => 250
      | _              => 150
      end
  end.

(* Fentanyl induction dose range (mcg/kg x100):
   Standard:   100-200  (1.0-2.0 mcg/kg)
   Elderly:     50-100  (0.5-1.0 mcg/kg)
   Pediatric:   100-200  (1.0-2.0 mcg/kg) *)

Definition fentanyl_induction_lo (age : AgeGroup) : nat :=
  match age with
  | Elderly   => 50
  | _         => 100
  end.

Definition fentanyl_induction_hi (age : AgeGroup) : nat :=
  match age with
  | Elderly   => 100
  | _         => 200
  end.

(******************************************************************************)
(* SECTION 3: DOSE RANGE VALIDITY                                             *)
(******************************************************************************)

(* A dose (scaled) is within the therapeutic window *)
Definition propofol_dose_safe
    (asa : ASAClass) (age : AgeGroup) (dose_x100 : nat) : bool :=
  Nat.leb (propofol_induction_lo asa age) dose_x100 &&
  Nat.leb dose_x100 (propofol_induction_hi asa age).

Definition fentanyl_dose_safe (age : AgeGroup) (dose_x100 : nat) : bool :=
  Nat.leb (fentanyl_induction_lo age) dose_x100 &&
  Nat.leb dose_x100 (fentanyl_induction_hi age).

(* Lo <= Hi for every ASA/age combination — the window is non-empty *)
Theorem propofol_window_nonempty : forall asa age,
  propofol_induction_lo asa age <= propofol_induction_hi asa age.
Proof.
  intros [] []; simpl; lia.
Qed.

Theorem fentanyl_window_nonempty : forall age,
  fentanyl_induction_lo age <= fentanyl_induction_hi age.
Proof.
  intros []; simpl; lia.
Qed.

(* The lower bound dose is always safe *)
Theorem propofol_lo_is_safe : forall asa age,
  propofol_dose_safe asa age (propofol_induction_lo asa age) = true.
Proof.
  intros asa age.
  unfold propofol_dose_safe.
  rewrite andb_true_iff. split.
  - apply Nat.leb_refl.
  - apply Nat.leb_le. apply propofol_window_nonempty.
Qed.

Theorem fentanyl_lo_is_safe : forall age,
  fentanyl_dose_safe age (fentanyl_induction_lo age) = true.
Proof.
  intros age.
  unfold fentanyl_dose_safe.
  rewrite andb_true_iff. split.
  - apply Nat.leb_refl.
  - apply Nat.leb_le. apply fentanyl_window_nonempty.
Qed.

(******************************************************************************)
(* SECTION 4: DOSE REDUCTION FOR ELDERLY AND HIGH ASA                        *)
(******************************************************************************)

(* Elderly patients always have a lower or equal upper bound than adults *)
Theorem elderly_lower_propofol_ceiling : forall asa,
  propofol_induction_hi asa Elderly <= propofol_induction_hi asa Adult.
Proof.
  intros []; simpl; lia.
Qed.

(* High ASA class reduces the adult propofol ceiling *)
Theorem high_asa_reduces_propofol_ceiling :
  propofol_induction_hi ASA_III Adult <= propofol_induction_hi ASA_I Adult.
Proof. simpl. lia. Qed.

(* Elderly fentanyl ceiling is strictly less than adult *)
Theorem elderly_lower_fentanyl_ceiling :
  fentanyl_induction_hi Elderly < fentanyl_induction_hi Adult.
Proof. simpl. lia. Qed.

(******************************************************************************)
(* SECTION 5: PREOPERATIVE CHECKLIST                                          *)
(******************************************************************************)

Record PreopChecklist : Type := mkPreop {
  preop_consent         : bool;
  preop_npo_confirmed   : bool;  (* nil per os — fasting confirmed *)
  preop_allergy_checked : bool;
  preop_iv_access       : bool;
  preop_monitor_on      : bool;  (* ECG, SpO2, BP *)
  preop_emergency_drugs : bool;  (* epinephrine, atropine, succinylcholine drawn *)
}.

Definition preop_safe (p : PreopChecklist) : bool :=
  preop_consent         p &&
  preop_npo_confirmed   p &&
  preop_allergy_checked p &&
  preop_iv_access       p &&
  preop_monitor_on      p &&
  preop_emergency_drugs p.

Theorem preop_safe_all_confirmed :
  preop_safe (mkPreop true true true true true true) = true.
Proof. reflexivity. Qed.

Theorem preop_unsafe_if_no_consent :
  preop_safe (mkPreop false true true true true true) = false.
Proof. reflexivity. Qed.

Theorem preop_safe_requires_all : forall p,
  preop_safe p = true ->
  preop_consent p = true /\
  preop_npo_confirmed p = true /\
  preop_allergy_checked p = true /\
  preop_iv_access p = true /\
  preop_monitor_on p = true /\
  preop_emergency_drugs p = true.
Proof.
  intros p H.
  unfold preop_safe in H.
  repeat rewrite andb_true_iff in H.
  tauto.
Qed.

(******************************************************************************)
(* SECTION 6: REVERSAL AGENTS                                                 *)
(******************************************************************************)

Inductive NMBAgent : Type :=
  | Succinylcholine     (* depolarizing; no reversal needed — wears off *)
  | Rocuronium          (* non-depolarizing; reversed by sugammadex *)
  | Vecuronium          (* non-depolarizing; reversed by neostigmine *)
  | Cisatracurium.      (* non-depolarizing; Hofmann elimination *)

Inductive ReversalAgent : Type :=
  | Sugammadex
  | Neostigmine
  | NoReversalNeeded.

Definition nmb_reversal (nmb : NMBAgent) : ReversalAgent :=
  match nmb with
  | Succinylcholine => NoReversalNeeded
  | Rocuronium      => Sugammadex
  | Vecuronium      => Neostigmine
  | Cisatracurium   => NoReversalNeeded   (* Hofmann *)
  end.

Lemma rocuronium_reversed_by_sugammadex :
  nmb_reversal Rocuronium = Sugammadex.
Proof. reflexivity. Qed.

Lemma succinylcholine_no_reversal :
  nmb_reversal Succinylcholine = NoReversalNeeded.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 7: OPIOID ANTAGONISM                                               *)
(******************************************************************************)

(* Naloxone dose for opioid reversal: 0.4-2 mg IV; titrate to effect.
   Modeled as a flag: if respiratory rate < threshold, give naloxone. *)

Definition respiratory_depression_threshold : nat := 8.  (* breaths/min *)

Definition naloxone_indicated (resp_rate : nat) : bool :=
  Nat.leb resp_rate respiratory_depression_threshold.

Lemma naloxone_at_8 : naloxone_indicated 8 = true.
Proof. reflexivity. Qed.

Lemma naloxone_not_at_12 : naloxone_indicated 12 = false.
Proof. reflexivity. Qed.

Theorem naloxone_monotone : forall r1 r2,
  r1 <= r2 ->
  naloxone_indicated r2 = true ->
  naloxone_indicated r1 = true.
Proof.
  intros r1 r2 Hle H.
  unfold naloxone_indicated in *.
  apply Nat.leb_le in H.
  apply Nat.leb_le.
  lia.
Qed.

(******************************************************************************)
(* SECTION 8: MALIGNANT HYPERTHERMIA TRIGGER CHECK                            *)
(******************************************************************************)

(* Malignant hyperthermia (MH) is triggered by volatile halogenated agents
   and succinylcholine in susceptible patients.
   Safe agents (TIVA): propofol, ketamine, opioids, benzodiazepines. *)

Inductive MaintenanceAgent : Type :=
  | Sevoflurane     (* volatile — MH trigger *)
  | Desflurane      (* volatile — MH trigger *)
  | Isoflurane      (* volatile — MH trigger *)
  | Propofol_TIVA   (* safe for MH-susceptible *)
  | Ketamine        (* safe for MH-susceptible *)
  | NitrousOxide.   (* non-triggering *)

Definition mh_trigger (agent : MaintenanceAgent) : bool :=
  match agent with
  | Sevoflurane  => true
  | Desflurane   => true
  | Isoflurane   => true
  | _            => false
  end.

Lemma sevoflurane_is_mh_trigger : mh_trigger Sevoflurane = true.
Proof. reflexivity. Qed.

Lemma propofol_tiva_safe : mh_trigger Propofol_TIVA = false.
Proof. reflexivity. Qed.

(* An MH-susceptible patient must not receive a triggering agent *)
Definition safe_for_mh_susceptible (agent : MaintenanceAgent) : bool :=
  negb (mh_trigger agent).

Theorem mh_safe_agent_nontriggering : forall agent,
  safe_for_mh_susceptible agent = true ->
  mh_trigger agent = false.
Proof.
  intros agent H.
  unfold safe_for_mh_susceptible in H.
  rewrite negb_true_iff in H. exact H.
Qed.

(******************************************************************************)
(* SECTION 9: FULL PATIENT RECORD AND SAFETY GATE                             *)
(******************************************************************************)

Record AnesthesiaPatient : Type := mkPatient {
  pt_asa       : ASAClass;
  pt_age_group : AgeGroup;
  pt_mallampati: MallampatiClass;
  pt_mh_risk   : bool;
  pt_preop     : PreopChecklist;
}.

(* Safe to proceed with induction given a chosen propofol dose and maintenance *)
Definition safe_to_induce
    (pt     : AnesthesiaPatient)
    (prop_dose : nat)
    (maintenance : MaintenanceAgent) : bool :=
  preop_safe (pt_preop pt) &&
  propofol_dose_safe (pt_asa pt) (pt_age_group pt) prop_dose &&
  (if pt_mh_risk pt then safe_for_mh_susceptible maintenance else true).

(* If induction is safe, preop checklist is complete *)
Theorem safe_induction_requires_preop : forall pt d m,
  safe_to_induce pt d m = true ->
  preop_safe (pt_preop pt) = true.
Proof.
  intros pt d m H.
  unfold safe_to_induce in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[Hpre _] _]. exact Hpre.
Qed.

(* MH-susceptible patient must not use a triggering agent *)
Theorem mh_patient_safe_maintenance : forall pt d m,
  safe_to_induce pt d m = true ->
  pt_mh_risk pt = true ->
  safe_for_mh_susceptible m = true.
Proof.
  intros pt d m H Hmh.
  unfold safe_to_induce in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[Hpre Hdose] Hmaint].
  rewrite Hmh in Hmaint. exact Hmaint.
Qed.

(******************************************************************************)
(* SECTION 10: SUMMARY                                                        *)
(******************************************************************************)

(*
  This file formalizes key anesthesia dosing safety rules in Coq.

  Structure:
    1. Patient classification: ASA I-VI, age groups, Mallampati airway.
    2. Dose windows (scaled integers x100):
       - Propofol induction: varies by ASA and age (50-350 mg/kg x100).
       - Fentanyl induction: varies by age (50-200 mcg/kg x100).
    3. Dose safety predicates: dose within therapeutic window.
    4. Key dose range theorems:
       - Windows are non-empty for all ASA/age combinations.
       - Lower bound dose is always safe.
       - Elderly and high-ASA patients have lower ceilings.
    5. Preoperative checklist: 6-item boolean record; all must pass.
    6. Neuromuscular blockade reversal agents.
    7. Naloxone indication: respiratory rate <= 8 breaths/min.
    8. Malignant hyperthermia trigger check: volatile agents are unsafe
       for susceptible patients; TIVA is safe.
    9. Full patient safety gate: preop + dose + MH agent check.

  All proofs closed; no Admitted lemmas.
*)
