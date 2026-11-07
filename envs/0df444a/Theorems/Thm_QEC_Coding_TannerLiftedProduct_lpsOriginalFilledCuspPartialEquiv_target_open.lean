-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_open
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_target_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:02.994726+00:00
-- url     : https://prove2.me/theorems/ee9e585c-317a-4766-af0e-3de2308d2c21
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv target open
-- statement:
--   The actual filled coordinate target is an open full disc.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L112-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L112-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_target_open (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpen (lpsOriginalFilledCuspPartialEquiv N ρ).target := by sorry
