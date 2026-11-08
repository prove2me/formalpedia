-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:06.227722+00:00
-- url     : https://prove2.me/theorems/d7fe85e9-4757-4bec-b3be-51076f877684
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eigenvalue is Big O of residual bound
-- statement:
--   Optimal residual growth gives the sharp-rate Hecke estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L480-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L480-L493

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

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
    (a : LPSResiduePrime p) (C : ℝ) (hC : 0 ≤ C)
    (hResidual : ∀ n : ℕ,
      |lpsCenteredThetaResidual a (2 * n)| ≤
        C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n))
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (t : ℝ) (ht : Real.sqrt (p : ℝ) < t) :
    (fun n : ℕ =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
      =O[atTop] fun n : ℕ => t ^ (2 * n) := by sorry
