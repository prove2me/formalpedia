-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_lpsHeckePolynomial_eigenvalue_le_residual_add_cancellation
-- name    : QEC.Coding.TannerLiftedProduct.two_mul_lpsHeckePolynomial_eigenvalue_le_residual_add_cancellation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:43.421452+00:00
-- url     : https://prove2.me/theorems/62ef20aa-bcad-4b25-bb07-c2f4ea93c9a8
-- title:
--   Tanner Lifted Product: two mul lps Hecke Polynomial eigenvalue le residual add cancellation
-- statement:
--   Residual shorthand for the preceding one-eigenvalue arithmetic bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L342-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L342-L353

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

theorem QEC.Coding.TannerLiftedProduct.two_mul_lpsHeckePolynomial_eigenvalue_le_residual_add_cancellation
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    2 * (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      lpsCenteredThetaResidual a (2 * n) +
        2 * ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by sorry
