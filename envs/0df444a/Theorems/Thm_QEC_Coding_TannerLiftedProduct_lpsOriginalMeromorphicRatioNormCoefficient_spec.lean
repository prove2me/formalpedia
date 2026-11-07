-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioNormCoefficient_spec
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioNormCoefficient_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:36:51.44431+00:00
-- url     : https://prove2.me/theorems/f1b89937-65ec-411a-ada2-5d10a2a3400c
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Norm Coefficient spec
-- statement:
--   The actual j-polynomial has bounded degree and exactly recovers the genuine norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L101-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L101-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioNormCoefficient_spec
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ) :
    (lpsOriginalMeromorphicRatioNormCoefficient N k A B c).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) ∧ ∀ τ : ℍ,
    lpsOriginalMeromorphicRatioNorm N k A B c τ =
      ModularForm.discriminant τ ^ (k * Nat.card (LPSOriginalMeromorphicCosets N)) *
        (lpsOriginalMeromorphicRatioNormCoefficient N k A B c).eval (lpsOriginalJInvariant τ) := by sorry
