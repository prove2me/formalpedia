-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:12.481216+00:00
-- url     : https://prove2.me/theorems/09af0655-e0a9-4f64-86ad-127a7537474e
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param injective
-- statement:
--   The genuine filled-disc parametrization is injective by the proved inverse laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L313-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L313-L319

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_injective (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Function.Injective (lpsOriginalFilledCuspParam N c) := by sorry
