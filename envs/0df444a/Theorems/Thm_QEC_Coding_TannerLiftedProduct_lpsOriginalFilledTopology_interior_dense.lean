-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_dense
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:02:09.962207+00:00
-- url     : https://prove2.me/theorems/2f5600d8-fce2-48c0-b198-d6b716a495e5
-- title:
--   Tanner Lifted Product: lps Original Filled Topology interior dense
-- statement:
--   Density of the actual original interior at every genuine added cusp; used by whole-curve connectedness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledConnected.lean#L23-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledConnected.lean#L23-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ClusterPt
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_dense (N : ℕ) [NeZero N] :
    letI := lpsOriginalFilledTopology N
    DenseRange (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by sorry
