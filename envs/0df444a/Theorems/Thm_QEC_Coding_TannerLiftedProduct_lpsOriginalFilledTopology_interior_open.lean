-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_open
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:20.24967+00:00
-- url     : https://prove2.me/theorems/33bdc2b4-68be-4adc-847d-da16bfb7ea3c
-- title:
--   Tanner Lifted Product: lps Original Filled Topology interior open
-- statement:
--   The original interior injection is PROVED open in the genuine filled topology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L113-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L113-L125

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_open (N : ℕ) [NeZero N] :
    @IsOpenMap _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by sorry
