-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_cusp_mem
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cusp_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:42.933461+00:00
-- url     : https://prove2.me/theorems/a87f782d-94c4-4300-bcf6-6a94c30018cb
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv cusp mem
-- statement:
--   The genuine added cusp belongs to its true filled chart source.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L108-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L108-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_cusp_mem (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Sum.inr (lpsOriginalCuspOrbit N ρ)∈(lpsOriginalFilledCuspPartialEquiv N ρ).source := by sorry
