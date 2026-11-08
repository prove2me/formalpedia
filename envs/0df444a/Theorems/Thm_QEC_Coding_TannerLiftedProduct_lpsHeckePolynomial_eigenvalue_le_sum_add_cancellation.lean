-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:59:03.818378+00:00
-- url     : https://prove2.me/theorems/1e723c0d-c82c-4afe-bf75-94180c2fc260
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eigenvalue le sum add cancellation
-- statement:
--   Cancellation control for one centered LPS eigenvalue: the even Hecke
--   value is bounded by the exact spectral sum plus the universal Chebyshev
--   lower-bound budget for all other eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L287-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L287-L314

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredAdjacencyEuclidean_isSymmetric

set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      (∑ j : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl j)) +
        ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by sorry
