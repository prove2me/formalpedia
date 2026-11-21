-- Prove2me | Theorems.Thm_RiemannMasullo_compactSpace_units_of_compactSpace
-- name    : RiemannMasullo.compactSpace_units_of_compactSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:16:03.282186+00:00
-- url     : https://prove2.me/theorems/7bdd6486-a6f3-4441-982d-3831b8c0bc72
-- title:
--   Riemann Masullo: compact Space units of compact Space
-- statement:
--   The units of a compact Hausdorff topological monoid form a compact space.
--
--   Source: https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/ForMathlib/Topology/Algebra/Group/Units.lean#L15-L30
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/ForMathlib/Topology/Algebra/Group/Units.lean#L15-L30

module
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Compactness.Compact
public import Definitions.Def_RiemannMasullo_ForMathlib_Topology_Algebra_Group_Units
set_option autoImplicit false
@[expose] public section
public section
open RiemannMasullo
open Topology

theorem RiemannMasullo.compactSpace_units_of_compactSpace (M : Type*) [Monoid M]
    [TopologicalSpace M] [T2Space M] [ContinuousMul M] [CompactSpace M] :
    CompactSpace Mˣ := by sorry
