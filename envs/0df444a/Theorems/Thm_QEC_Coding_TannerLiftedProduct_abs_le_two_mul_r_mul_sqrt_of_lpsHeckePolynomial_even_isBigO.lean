-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_two_mul_r_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_two_mul_r_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:25.247205+00:00
-- url     : https://prove2.me/theorems/19b7ea7b-7396-4448-a9a6-5e91a027fe38
-- title:
--   Tanner Lifted Product: abs le two mul r mul sqrt of lps Hecke Polynomial even is Big O
-- statement:
--   Even Hecke growth at every rate above `r√p` bounds the eigenvalue by
--   `2r√p`, for any `r ≥ 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L81-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L81-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.abs_le_two_mul_r_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    {p : ℝ} (hp : 0 < p) (lambda rBound : ℝ) (hrBound : 1 ≤ rBound)
    (h : ∀ t : ℝ, rBound * Real.sqrt p < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ p (2 * n)).eval lambda) =O[atTop]
          fun n : ℕ => t ^ (2 * n)) :
    |lambda| ≤ 2 * rBound * Real.sqrt p := by sorry
