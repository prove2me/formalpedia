-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_log_inv_selectedDoublePowerTarget
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.log_inv_selectedDoublePowerTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:33:47.80553+00:00
-- url     : https://prove2.me/theorems/cacb3756-d0e6-4713-82d7-d0862a22a3dd
-- title:
--   HH18 Sublogarithmic Entropy: log inv selected Double Power Target
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the log inv selected Double Power Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L322-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L322-L328

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.log_inv_selectedDoublePowerTarget {q : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) :
    Real.log (1 / selectedDoublePowerTarget q A D j z) =
      (parameterDistance A D j : ℝ) ^ z * Real.log (1 / q) := by sorry
