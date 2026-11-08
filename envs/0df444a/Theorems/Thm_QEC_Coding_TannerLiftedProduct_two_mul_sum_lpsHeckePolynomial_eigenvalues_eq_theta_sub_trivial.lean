-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:56:28.726207+00:00
-- url     : https://prove2.me/theorems/6cebfbb3-a100-41d0-b30a-9b76a3df9ee0
-- title:
--   Tanner Lifted Product: two mul sum lps Hecke Polynomial eigenvalues eq theta sub trivial
-- statement:
--   Exact real spectral-sum form of the centered LPS theta trace formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L225-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L225-L247

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

theorem QEC.Coding.TannerLiftedProduct.two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * (∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)) =
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℝ) ^ i) -
          (lpsHeckePolynomial ℝ (p : ℝ) n).eval 0) := by sorry
