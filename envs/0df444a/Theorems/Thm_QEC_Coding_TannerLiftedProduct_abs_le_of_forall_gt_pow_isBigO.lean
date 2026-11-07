-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_forall_gt_pow_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_of_forall_gt_pow_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:30.770559+00:00
-- url     : https://prove2.me/theorems/63ab776a-c0ff-4db0-8320-fc748b087947
-- title:
--   Tanner Lifted Product: abs le of forall gt pow is Big O
-- statement:
--   If `|x|^n` has every exponential upper rate strictly above `r`, then
--   `|x| ≤ r`.  This is the closed-boundary passage used in the LPS moment
--   argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L38-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L38-L54

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.abs_le_of_forall_gt_pow_isBigO
    {x r : ℝ} (hr : 0 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ n) =O[atTop]
        fun n : ℕ => s ^ n) :
    |x| ≤ r := by sorry
