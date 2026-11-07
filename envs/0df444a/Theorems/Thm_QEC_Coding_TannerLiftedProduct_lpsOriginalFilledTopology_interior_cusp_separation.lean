-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_cusp_separation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_cusp_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:50.560146+00:00
-- url     : https://prove2.me/theorems/a2a7044b-11c3-4da4-b70f-aa49e3fac940
-- title:
--   Tanner Lifted Product: lps Original Filled Topology interior cusp separation
-- statement:
--   Actual height bounds give disjoint OPEN neighborhoods of every interior point and genuine cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L137-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean#L137-L199

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_cusp_separation (N : ℕ) [NeZero N]
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    ∃ u v : Set (LPSOriginalFilledCurve N),
      IsOpen[lpsOriginalFilledTopology N] u ∧ IsOpen[lpsOriginalFilledTopology N] v ∧
        Sum.inl y∈u ∧ Sum.inr c∈v ∧ Disjoint u v := by sorry
