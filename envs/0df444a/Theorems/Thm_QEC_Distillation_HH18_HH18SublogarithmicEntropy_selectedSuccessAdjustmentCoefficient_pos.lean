-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selectedSuccessAdjustmentCoefficient_pos
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedSuccessAdjustmentCoefficient_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:34:27.714441+00:00
-- url     : https://prove2.me/theorems/05ba2d53-9107-41d5-a1cf-fc032a1c31ed
-- title:
--   HH18 Sublogarithmic Entropy: selected Success Adjustment Coefficient pos
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the selected Success Adjustment Coefficient pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L380-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L380-L384

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedSuccessAdjustmentCoefficient_pos {q sigma : ℝ} {A D j : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma) :
    0 < selectedSuccessAdjustmentCoefficient q sigma A D j := by sorry
