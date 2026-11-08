-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:48.22452+00:00
-- url     : https://prove2.me/theorems/cab7b7d0-45e7-4617-aaac-ddfba7461bca
-- title:
--   Tanner Lifted Product: abs le two mul sqrt of lps Hecke Polynomial even is Big O
-- statement:
--   Sharp Hecke-growth criterion for the Ramanujan interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L128-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L128-L136

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    {p : ℝ} (hp : 0 < p) (lambda : ℝ)
    (h : ∀ t : ℝ, Real.sqrt p < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ p (2 * n)).eval lambda) =O[atTop]
          fun n : ℕ => t ^ (2 * n)) :
    |lambda| ≤ 2 * Real.sqrt p := by sorry
