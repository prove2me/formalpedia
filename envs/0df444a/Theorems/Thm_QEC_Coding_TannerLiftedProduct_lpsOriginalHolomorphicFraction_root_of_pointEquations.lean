-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFraction_root_of_pointEquations
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFraction_root_of_pointEquations
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:51:31.548733+00:00
-- url     : https://prove2.me/theorems/9ba56110-4f8c-43c1-873c-e7e77474f098
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Fraction root of point Equations
-- statement:
--   Actual point equations away from denominator zeros yield a fraction-field root by homogenization and domain cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicFractionRoot.lean#L28-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicFractionRoot.lean#L28-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Mathlib.Algebra.Polynomial.Homogenize
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFraction_root_of_pointEquations
    (p : Polynomial LPSOriginalHolomorphicRing) (r : ℕ) (hp : p.natDegree ≤ r)
    (A B : LPSOriginalHolomorphicRing) (hB : B ≠ 0)
    (hpoint : ∀ τ : ℍ, B.val τ ≠ 0 →
      p.eval₂ (lpsOriginalHolomorphicPointEvaluation τ)
        (A.val τ / B.val τ) = 0) :
    p.eval₂ (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
      ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField A) /
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField B)) = 0 := by sorry
