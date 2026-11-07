-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_forall_gt_evenPow_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_of_forall_gt_evenPow_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:17.472218+00:00
-- url     : https://prove2.me/theorems/14d82929-de59-44f0-99c2-82da3b38d475
-- title:
--   Tanner Lifted Product: abs le of forall gt even Pow is Big O
-- statement:
--   An even-power version of the preceding criterion.  This is convenient
--   for self-adjoint adjacency spectra because all summands in an even spectral
--   moment are nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L59-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L59-L84

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.abs_le_of_forall_gt_evenPow_isBigO
    {x r : ℝ} (hr : 0 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ r := by sorry
