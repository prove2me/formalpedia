-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_upstairs_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_upstairs_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:06:38.68771+00:00
-- url     : https://prove2.me/theorems/d28e3458-cd1a-4984-b785-8eccdb4f8f23
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Function upstairs holomorphic
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normalized Filled Function upstairs holomorphic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizedIntegral.lean#L62-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizedIntegral.lean#L62-L86

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_upstairs_holomorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hno : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => lpsOriginalNormalizedFilledFunction N hN F (Sum.inl ⟦τ⟧)) := by sorry
