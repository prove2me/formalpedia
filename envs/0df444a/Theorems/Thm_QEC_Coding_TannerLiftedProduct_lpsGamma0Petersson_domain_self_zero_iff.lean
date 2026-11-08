-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Petersson_domain_self_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_domain_self_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:55:17.60853+00:00
-- url     : https://prove2.me/theorems/509fec1d-27c0-4d3f-add3-c1d0f1376f3b
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson domain self zero iff
-- statement:
--   The original positive-definite pairing detects zero cusp forms on every genuine Gamma0 domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L137-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L137-L142

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_domain_self_zero_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    (∫τ in s,petersson 2 f f τ) = 0 ↔ f = 0 := by sorry
