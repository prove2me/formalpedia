-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_ratio_pow_eq_target_log_rpow_quotient
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_eq_target_log_rpow_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:34:18.72989+00:00
-- url     : https://prove2.me/theorems/6055bf08-c0b5-4e84-b671-1a3e39445043
-- title:
--   HH18 Sublogarithmic Entropy: selected ratio pow eq target log rpow quotient
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the selected ratio pow eq target log rpow quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L354-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L354-L369

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_eq_target_log_rpow_quotient
    {q : ℝ} {A D j z : Nat} (hq0 : 0 < q) (hq1 : q < 1)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z =
      Real.rpow (Real.log (1 / selectedDoublePowerTarget q A D j z))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) /
        Real.rpow (Real.log (1 / q))
          (concatenationExponent (parameterLength A D j)
            (parameterDimension A D j) (parameterDistance A D j)) := by sorry
