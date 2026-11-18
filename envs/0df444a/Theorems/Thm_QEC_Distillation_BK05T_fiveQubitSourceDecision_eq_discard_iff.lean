-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitSourceDecision_eq_discard_iff
-- name    : QEC.Distillation.BK05T.fiveQubitSourceDecision_eq_discard_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-17T19:09:33.442203+00:00
-- url     : https://prove2.me/theorems/56cdd158-0132-40bc-b952-1303745211ad
-- title:
--   BK05 T: five Qubit Source Decision eq discard iff
-- statement:
--   The BK05 T construction uses the five Qubit Source Decision eq discard iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L305-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L305-L309

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct

theorem QEC.Distillation.BK05T.fiveQubitSourceDecision_eq_discard_iff
    (syndrome : JointSyndrome FiveQubitCheckIndex) :
    fiveQubitSourceDecision syndrome = .discardBeforeDecode ↔
      syndrome ≠ fiveQubitPositiveSyndrome := by sorry
