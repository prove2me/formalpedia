-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_recovery
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:35:56.25469+00:00
-- url     : https://prove2.me/theorems/f6c3dc11-6e08-402d-a296-376c992cc1f2
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Equation recovery
-- statement:
--   The genuine Delta power times the constructed equation recovers the literal coset product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L140-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L140-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_recovery
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    Polynomial.C (ModularForm.discriminant τ ^
      (k*Nat.card (LPSOriginalMeromorphicCosets N))) *
        (lpsOriginalMeromorphicRatioEquation N k A B).map
          (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) =
      lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ := by sorry
