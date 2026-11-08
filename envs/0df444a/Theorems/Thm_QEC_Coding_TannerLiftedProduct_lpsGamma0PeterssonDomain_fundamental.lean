-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:53:35.892222+00:00
-- url     : https://prove2.me/theorems/ef1b9b48-de0b-40cc-8a2d-6af8ab46e673
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson Domain fundamental
-- statement:
--   The original-representative domain is fundamental for actual effective Gamma0, including level zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L97-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L97-L99

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_fundamental (N : ℕ) :
    IsFundamentalDomain (lpsEffectiveGamma0 N) (lpsGamma0PeterssonDomain N) volume := by sorry
