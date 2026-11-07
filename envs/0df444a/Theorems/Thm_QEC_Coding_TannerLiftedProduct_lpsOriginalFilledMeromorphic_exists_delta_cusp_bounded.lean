-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:31:59.528415+00:00
-- url     : https://prove2.me/theorems/a5f6a7c2-bfa9-4759-a09f-fff32d326745
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic exists delta cusp bounded
-- statement:
--   One genuine Delta power makes an arbitrary original meromorphic function bounded at every cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L193-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L193-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ k : ℕ, ∀ ρ : SL(2,ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by sorry
