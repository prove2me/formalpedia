-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspClosedPatch_cusp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_cusp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:42.735713+00:00
-- url     : https://prove2.me/theorems/5633303d-ef62-4a29-b90b-d4b2a524be1c
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Closed Patch cusp
-- statement:
--   Each closed patch contains its correct genuine added cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L190-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L190-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_cusp (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Sum.inr c∈lpsOriginalFilledCuspClosedPatch N c := by sorry
