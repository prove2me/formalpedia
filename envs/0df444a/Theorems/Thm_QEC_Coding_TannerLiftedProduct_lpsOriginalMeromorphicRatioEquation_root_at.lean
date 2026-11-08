-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_root_at
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_root_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:04.885912+00:00
-- url     : https://prove2.me/theorems/c6fc54e9-4add-4471-95b2-f16630700c47
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Equation root at
-- statement:
--   A literal numerator-denominator relation at one point gives the actual coset equation root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L178-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L178-L195

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_root_at
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (t : ℂ) (ht : A τ = B τ*t) :
    (lpsOriginalMeromorphicRatioEquation N k A B).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) t = 0 := by sorry
