-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_sources_disjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_sources_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:09.301348+00:00
-- url     : https://prove2.me/theorems/56b0bcbc-4d0a-4648-a630-212ba5411aed
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Partial Equiv sources disjoint
-- statement:
--   Different true cusp labels have disjoint filled chart sources.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L154-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L154-L164

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspPartialEquiv_sources_disjoint (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (h : lpsOriginalCuspOrbit N ρ≠lpsOriginalCuspOrbit N ρ') :
    Disjoint (lpsOriginalFilledCuspPartialEquiv N ρ).source
      (lpsOriginalFilledCuspPartialEquiv N ρ').source := by sorry
