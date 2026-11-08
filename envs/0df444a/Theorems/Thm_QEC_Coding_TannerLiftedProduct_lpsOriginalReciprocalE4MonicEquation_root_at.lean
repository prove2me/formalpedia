-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalE4MonicEquation_root_at
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4MonicEquation_root_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:33:23.355206+00:00
-- url     : https://prove2.me/theorems/16ef81f6-c559-4080-852c-1abb31f39e57
-- title:
--   Tanner Lifted Product: lps Original Reciprocal E4 Monic Equation root at
-- statement:
--   At a genuine nonzero-j point the reflected monic equation annihilates the literal E4 ratio.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L198-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L198-L213

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4MonicEquation_root_at
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (t : ℂ) (hj : lpsOriginalJInvariant τ ≠ 0)
    (ht : A τ = (ModularForm.E₄ τ^3)^k*t) :
    (lpsOriginalReciprocalE4MonicEquation N k A).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)⁻¹) t = 0 := by sorry
