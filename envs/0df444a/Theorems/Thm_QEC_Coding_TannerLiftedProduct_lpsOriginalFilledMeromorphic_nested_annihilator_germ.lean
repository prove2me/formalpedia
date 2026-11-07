-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_nested_annihilator_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_nested_annihilator_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:37:35.499716+00:00
-- url     : https://prove2.me/theorems/8f075bb9-e4a1-459e-aed3-9a1ba16d91d6
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic nested annihilator germ
-- statement:
--   The true pointwise equation descends to the actual original meromorphic germ field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L304-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L304-L340

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_nested_annihilator_germ
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (Φ : Polynomial (Polynomial ℂ))
    (hΦ : ∀ τ : ℍ, Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (F (Sum.inl ⟦τ⟧)) = 0) :
    Φ.eval₂ ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))))
      (lpsOriginalFilledMeromorphicRestriction N hN F hF) = 0 := by sorry
