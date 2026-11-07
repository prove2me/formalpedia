-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledHolomorphic_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledHolomorphic_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:39:24.679014+00:00
-- url     : https://prove2.me/theorems/4fc9cd40-c37a-43f8-bb25-eae65a115b05
-- title:
--   Tanner Lifted Product: lps Original Filled Holomorphic integral
-- statement:
--   Literal restriction-field integrality over SAME C[j], not merely algebraicity over C(j).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L136-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicIntegral.lean#L136-L150

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledHolomorphic_integral
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))) :
    letI := ((lpsOriginalFullMeromorphicJFractionEmbedding N hN).comp
      (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).toAlgebra
    IsIntegral (Polynomial ℂ) (lpsOriginalFilledMeromorphicRestriction N hN F hF) := by sorry
