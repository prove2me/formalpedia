-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_cusp_bounded
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:19:39.8932+00:00
-- url     : https://prove2.me/theorems/1d933be5-9f2e-4d8d-b005-a740cc46e3b8
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Function cusp bounded
-- statement:
--   The analytic normalized cusp extension gives genuine boundedness near every cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L101-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNormalization.lean#L101-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_bounded
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (ρ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      lpsOriginalNormalizedFilledFunction N hN F
        (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by sorry
