-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_delta_cusp_bounded
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_delta_cusp_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:32:03.938979+00:00
-- url     : https://prove2.me/theorems/27f2f07c-b570-4dec-8654-ece1ddc25667
-- title:
--   Tanner Lifted Product: lps Original Filled Meromorphic delta cusp bounded
-- statement:
--   True cusp phase, integer width and Delta zero make the cleared pullback bounded at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L153-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L153-L188

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_delta_cusp_bounded
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ)
    (hf : letI := lpsOriginalFilledTopology N
      AnalyticAt ℂ (fun q : ℂ => q^k *
      F ((lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm q)) 0) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by sorry
