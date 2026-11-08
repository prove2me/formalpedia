-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_lpsCenteredEigenvalue_le_four_mul_sqrt_of_theta_bound
-- name    : QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_four_mul_sqrt_of_theta_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:59:17.879307+00:00
-- url     : https://prove2.me/theorems/62fa4f2e-f6b9-4f3e-8cb6-286b7e3b5396
-- title:
--   Tanner Lifted Product: abs lps Centered Eigenvalue le four mul sqrt of theta bound
-- statement:
--   The relaxed theta coefficient bound controls every centered LPS
--   eigenvalue at the `4√p` radius required by the PK22 schedule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L497-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L497-L523

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

theorem QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_four_mul_sqrt_of_theta_bound
    (a : LPSResiduePrime p)
    (hBound : HasFourSqrtCenteredThetaCoefficientBound a)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      4 * Real.sqrt (p : ℝ) := by sorry
