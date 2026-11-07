-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_openEmbedding
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_openEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:41:26.441731+00:00
-- url     : https://prove2.me/theorems/0a0041af-7f49-4c27-8bf0-01742056c280
-- title:
--   Tanner Lifted Product: lps Original Filled Topology interior open Embedding
-- statement:
--   The ORIGINAL quotient is an OPEN EMBEDDING retaining its topology inside the true filling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L128-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L128-L134

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_openEmbedding (N : ℕ) [NeZero N] :
    @Topology.IsOpenEmbedding _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by sorry
