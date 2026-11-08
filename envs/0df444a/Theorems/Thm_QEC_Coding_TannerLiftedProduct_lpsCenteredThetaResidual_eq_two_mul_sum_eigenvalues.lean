-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_eq_two_mul_sum_eigenvalues
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_eq_two_mul_sum_eigenvalues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:18.161262+00:00
-- url     : https://prove2.me/theorems/eeba7759-f228-4710-b3d0-bc77a5f27b5d
-- title:
--   Tanner Lifted Product: lps Centered Theta Residual eq two mul sum eigenvalues
-- statement:
--   The centered theta residual is exactly twice the real spectral Hecke
--   sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L274-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L274-L282

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

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_eq_two_mul_sum_eigenvalues
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a n =
      2 * (∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)) := by sorry
