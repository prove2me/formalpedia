-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:46.928068+00:00
-- url     : https://prove2.me/theorems/8dcc1398-c852-4679-9aa1-545cb6f28e34
-- title:
--   Tanner Lifted Product: two mul lps Hecke Polynomial eigenvalue le theta add cancellation
-- statement:
--   Fully arithmetic upper bound for one even Hecke value.  After this
--   theorem, the only family-specific quantity on the right is the explicit
--   theta coefficient; all possible spectral cancellation has been paid for by
--   the universal `(2n+1)pⁿ` budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L320-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L320-L339

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

theorem QEC.Coding.TannerLiftedProduct.two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    2 * (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ (2 * n))
            (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ j ∈ Finset.range (2 * n + 1), (p : ℝ) ^ j) -
          (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval 0) +
        2 * ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by sorry
