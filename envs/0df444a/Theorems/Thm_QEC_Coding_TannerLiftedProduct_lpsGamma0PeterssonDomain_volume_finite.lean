-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_volume_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_volume_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:55:26.411584+00:00
-- url     : https://prove2.me/theorems/5c5f266c-b114-460a-83f0-4e1dac197b9d
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson Domain volume finite
-- statement:
--   Every positive-level original Gamma0 integration domain has finite actual hyperbolic volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L152-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L152-L155

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_volume_finite (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (lpsGamma0PeterssonDomain N) < ∞ := by sorry
