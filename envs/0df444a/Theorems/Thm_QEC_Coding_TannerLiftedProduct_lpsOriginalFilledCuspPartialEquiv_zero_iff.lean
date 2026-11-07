-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:45:48.528305+00:00
-- url     : https://prove2.me/theorems/d65a5aa6-75b0-4728-aac1-76c3ef1af000
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv zero iff
-- statement:
--   On the actual source, zero is precisely the correct genuine cusp point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L135-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L135-L144

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_zero_iff (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (x : LPSOriginalFilledCurve N) (hx : x∈(lpsOriginalFilledCuspPartialEquiv N ρ).source) :
    lpsOriginalFilledCuspPartialEquiv N ρ x=0 ↔ x=Sum.inr (lpsOriginalCuspOrbit N ρ) := by sorry
