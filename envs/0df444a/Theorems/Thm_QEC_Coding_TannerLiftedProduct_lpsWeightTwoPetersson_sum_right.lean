-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_sum_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_sum_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:57:37.713654+00:00
-- url     : https://prove2.me/theorems/5bf5c158-ee62-484f-ab6c-8ff812e45ae6
-- title:
--   Tanner Lifted Product: lps Weight Two Petersson sum right
-- statement:
--   The actual weight-two integrand preserves finite sums in its second factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L66-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L66-L70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_sum_right {ι : Type*} [Fintype ι] (f : ℍ → ℂ)
    (G : ι → ℍ → ℂ) (τ : ℍ) :
    petersson 2 f (∑i,G i) τ = ∑i,petersson 2 f (G i) τ := by sorry
