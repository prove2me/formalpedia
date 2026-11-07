-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspClosedPatch_disc_inside
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_disc_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:38.572196+00:00
-- url     : https://prove2.me/theorems/9653ce67-d8fe-481c-966a-2b8f83d7ffc6
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Closed Patch disc inside
-- statement:
--   The genuine closed disc is strictly inside the actual filled chart target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L175-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L175-L187

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspClosedPatch_disc_inside (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Metric.closedBall (0:ℂ) (Real.exp
      (-2*Real.pi*2/(lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty))⊆
        (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target := by sorry
