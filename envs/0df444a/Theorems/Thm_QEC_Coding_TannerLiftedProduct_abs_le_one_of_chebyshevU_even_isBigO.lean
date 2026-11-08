-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_one_of_chebyshevU_even_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_one_of_chebyshevU_even_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:03:44.881636+00:00
-- url     : https://prove2.me/theorems/983bbff0-9d42-4cbc-9d5a-db3a013bc669
-- title:
--   Tanner Lifted Product: abs le one of chebyshev U even is Big O
-- statement:
--   Exponential control of even Chebyshev evaluations above one gives the
--   sharp interval `[-1,1]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L70-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L70-L77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.abs_le_one_of_chebyshevU_even_isBigO
    (x : ℝ)
    (h : ∀ s : ℝ, 1 < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ 1 := by sorry
