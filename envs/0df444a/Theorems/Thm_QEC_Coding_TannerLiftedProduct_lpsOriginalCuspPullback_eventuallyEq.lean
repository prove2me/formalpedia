-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPullback_eventuallyEq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPullback_eventuallyEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:07:00.393797+00:00
-- url     : https://prove2.me/theorems/47633432-169a-4402-b99d-efff21ec7e4e
-- title:
--   Tanner Lifted Product: lps Original Cusp Pullback eventually Eq
-- statement:
--   Punctured equality in the actual cusp chart gives equality of genuine cusp pullbacks near infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L20-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L20-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPullback_eventuallyEq
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F G : LPSOriginalFilledCurve N → ℂ)
    (he : letI := lpsOriginalFilledTopology N
      (F ∘ (lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm)
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (G ∘ (lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm)) :
    (fun τ : ℍ => F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))
      =ᶠ[UpperHalfPlane.atImInfty]
    (fun τ : ℍ => G (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by sorry
