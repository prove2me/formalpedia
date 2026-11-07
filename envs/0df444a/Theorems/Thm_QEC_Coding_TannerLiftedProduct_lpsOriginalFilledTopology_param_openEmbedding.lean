-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_openEmbedding
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_openEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:16.400968+00:00
-- url     : https://prove2.me/theorems/b40177d1-78da-4356-86d3-697960379638
-- title:
--   Tanner Lifted Product: lps Original Filled Topology param open Embedding
-- statement:
--   The true full cusp disc is an OPEN EMBEDDING in the actual filled topology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L104-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L104-L110

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_openEmbedding (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @Topology.IsOpenEmbedding _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by sorry
