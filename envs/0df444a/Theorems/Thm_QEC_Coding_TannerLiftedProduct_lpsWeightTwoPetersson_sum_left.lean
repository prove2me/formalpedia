-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_sum_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_sum_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:57:54.968707+00:00
-- url     : https://prove2.me/theorems/f247948b-c0b8-477a-8655-cc3874073434
-- title:
--   Tanner Lifted Product: lps Weight Two Petersson sum left
-- statement:
--   The actual weight-two integrand preserves finite sums in its conjugate-linear first factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L59-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L59-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_sum_left {ι : Type*} [Fintype ι] (F : ι → ℍ → ℂ)
    (g : ℍ → ℂ) (τ : ℍ) :
    petersson 2 (∑i,F i) g τ = ∑i,petersson 2 (F i) g τ := by sorry
