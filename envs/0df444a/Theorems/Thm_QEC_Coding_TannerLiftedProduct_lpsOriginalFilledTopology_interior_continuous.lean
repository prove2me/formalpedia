-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:22.206275+00:00
-- url     : https://prove2.me/theorems/4e7d06f3-f59d-4bf3-994d-716288fc6b61
-- title:
--   Tanner Lifted Product: lps Original Filled Topology interior continuous
-- statement:
--   The original interior injection is continuous for the specified genuine gluing topology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L45-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L45-L50

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_continuous (N : ℕ) [NeZero N] :
    @Continuous _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by sorry
