-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_target_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:41.449572+00:00
-- url     : https://prove2.me/theorems/72ddb808-c1c2-4c61-9913-d9760d2b7fba
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv target zero
-- statement:
--   The actual filled disc contains zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L117-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L117-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_target_zero (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    (0:ℂ)∈(lpsOriginalFilledCuspPartialEquiv N ρ).target := by sorry
