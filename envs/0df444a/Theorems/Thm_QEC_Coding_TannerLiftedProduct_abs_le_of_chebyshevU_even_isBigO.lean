-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_chebyshevU_even_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_of_chebyshevU_even_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:53:14.917296+00:00
-- url     : https://prove2.me/theorems/e06eadc8-f0f4-4490-9371-7dd8511151e9
-- title:
--   Tanner Lifted Product: abs le of chebyshev U even is Big O
-- statement:
--   Analytic Chebyshev endgame at any radius at least one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L43-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L43-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.abs_le_of_chebyshevU_even_isBigO
    (x r : ℝ) (hr : 1 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ r := by sorry
