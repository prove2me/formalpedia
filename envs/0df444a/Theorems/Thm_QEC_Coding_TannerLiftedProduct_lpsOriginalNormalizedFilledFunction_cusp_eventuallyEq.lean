-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:19:35.785039+00:00
-- url     : https://prove2.me/theorems/4e075401-7039-41b0-af50-97ed8bbdf15c
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Function cusp eventually Eq
-- statement:
--   Normalization preserves the actual cusp pullback germ near infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L58-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L58-L75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    (fun τ : ℍ => lpsOriginalNormalizedFilledFunction N hN F
      (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))
      =ᶠ[UpperHalfPlane.atImInfty]
    (fun τ : ℍ => F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by sorry
