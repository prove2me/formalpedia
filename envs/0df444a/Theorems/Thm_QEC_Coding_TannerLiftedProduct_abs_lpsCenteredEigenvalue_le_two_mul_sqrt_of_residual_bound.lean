-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound
-- name    : QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:59:36.141358+00:00
-- url     : https://prove2.me/theorems/c19593a6-efab-4640-92a8-510ddc9757dd
-- title:
--   Tanner Lifted Product: abs lps Centered Eigenvalue le two mul sqrt of residual bound
-- statement:
--   The optimal centered theta coefficient estimate implies the sharp
--   Ramanujan bound for every centered LPS adjacency eigenvalue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L527-L537
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L527-L537

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

theorem QEC.Coding.TannerLiftedProduct.abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound
    (a : LPSResiduePrime p) (hBound : HasOptimalCenteredThetaCoefficientBound a)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      2 * Real.sqrt (p : ℝ) := by sorry
