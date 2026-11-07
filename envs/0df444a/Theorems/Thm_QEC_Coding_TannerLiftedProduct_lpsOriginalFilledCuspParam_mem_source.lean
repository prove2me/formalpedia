-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_mem_source
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_mem_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:52.9236+00:00
-- url     : https://prove2.me/theorems/88d8cfaa-0c0e-4838-95db-45b850b76456
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param mem source
-- statement:
--   The genuine parametrization takes values in its actual original filled chart source.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L322-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L322-L327

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_mem_source (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target) :
    lpsOriginalFilledCuspParam N c q∈
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source := by sorry
