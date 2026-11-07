-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_closedPatch_isCompact
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_closedPatch_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:39.372285+00:00
-- url     : https://prove2.me/theorems/4ed226e4-0d19-44fb-88bc-1643ec13cc05
-- title:
--   Tanner Lifted Product: lps Original Filled Topology closed Patch is Compact
-- statement:
--   Each actual closed cusp patch is compact in the true filled topology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L62-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L62-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_closedPatch_isCompact (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @IsCompact (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspClosedPatch N c) := by sorry
