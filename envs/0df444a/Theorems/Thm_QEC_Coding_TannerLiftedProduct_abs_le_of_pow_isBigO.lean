-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_pow_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_of_pow_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:20:53.184178+00:00
-- url     : https://prove2.me/theorems/f40d998f-65ff-41b3-97bc-3a473abd648f
-- title:
--   Tanner Lifted Product: abs le of pow is Big O
-- statement:
--   A real exponential sequence can be big-O of another positive
--   exponential sequence only when its base is no larger.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L20-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L20-L33

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.abs_le_of_pow_isBigO
    {x r : ℝ} (hr : 0 < r)
    (h : (fun n : ℕ => |x| ^ n) =O[atTop]
      fun n : ℕ => r ^ n) :
    |x| ≤ r := by sorry
