-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_cusp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cusp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:31.015746+00:00
-- url     : https://prove2.me/theorems/30f20816-1ee8-4f53-8b43-38d0b9f0787c
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv cusp
-- statement:
--   The genuine added cusp maps to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L104-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L104-L105

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cusp (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    lpsOriginalFilledCuspPartialEquiv N ρ (Sum.inr (lpsOriginalCuspOrbit N ρ))=0 := by sorry
