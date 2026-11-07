-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_range
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:53.010033+00:00
-- url     : https://prove2.me/theorems/fdad547e-2c69-4528-8e4f-ad8e5a7697c8
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param range
-- statement:
--   The actual filled-disc parametrization has exactly the true filled chart source as its range.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L397-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L397-L408

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_range (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Set.range (lpsOriginalFilledCuspParam N c)=
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source := by sorry
