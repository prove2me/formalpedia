-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_ratio_pow_eq_rpow_depth_base
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_eq_rpow_depth_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:34:29.225811+00:00
-- url     : https://prove2.me/theorems/f02aa1b1-dbd0-43d4-aa14-b3954127d639
-- title:
--   HH18 Sublogarithmic Entropy: selected ratio pow eq rpow depth base
-- statement:
--   The HH18 Sublogarithmic Entropy construction uses the selected ratio pow eq rpow depth base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L344-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/TargetSchedule.lean#L344-L352

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_eq_rpow_depth_base (A D j z : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z =
      Real.rpow ((parameterDistance A D j : ℝ) ^ z)
        (concatenationExponent (parameterLength A D j)
          (parameterDimension A D j) (parameterDistance A D j)) := by sorry
