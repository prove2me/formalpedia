-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_ratio_pow_div_success_le_target_rpow
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_div_success_le_target_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:34:31.55359+00:00
-- url     : https://prove2.me/theorems/eda76eeb-4b1f-4c76-8ae0-2481d8f7091c
-- title:
--   HH18 Sublogarithmic Entropy: selected ratio pow div success le target rpow
-- statement:
--   A later adapter can apply this only after supplying an actual success lower
--   bound for its own construction; no count or error attachment occurs here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L388-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L388-L404

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_div_success_le_target_rpow
    {q sigma success : ℝ} {A D j z : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma)
    (hsuccess : sigma ≤ success) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z / success ≤
      selectedSuccessAdjustmentCoefficient q sigma A D j *
        Real.rpow (Real.log (1 / selectedDoublePowerTarget q A D j z))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) := by sorry
