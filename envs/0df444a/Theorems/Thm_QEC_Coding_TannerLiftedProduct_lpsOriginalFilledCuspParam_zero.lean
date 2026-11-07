-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:38:30.410561+00:00
-- url     : https://prove2.me/theorems/5b67d59e-9e5f-4aa5-95dc-c26698403daa
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param zero
-- statement:
--   Zero parametrizes exactly the corresponding genuine cusp orbit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L306-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L306-L310

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_zero (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq : q.val=0) : lpsOriginalFilledCuspParam N c q=Sum.inr c := by sorry
