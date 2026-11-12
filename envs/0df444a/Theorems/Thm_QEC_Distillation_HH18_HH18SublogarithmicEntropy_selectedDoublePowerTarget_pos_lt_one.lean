-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selectedDoublePowerTarget_pos_lt_one
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedDoublePowerTarget_pos_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:33:21.87431+00:00
-- url     : https://prove2.me/theorems/ea01c0cd-5564-475f-8b85-a840a00442a4
-- title:
--   HH18 Sublogarithmic Entropy: selected Double Power Target pos lt one
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the selected Double Power Target pos lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L303-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L303-L310

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedDoublePowerTarget_pos_lt_one {q : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < selectedDoublePowerTarget q A D j z ∧
      selectedDoublePowerTarget q A D j z < 1 := by sorry
