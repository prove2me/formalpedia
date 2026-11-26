-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_2
-- name    : Scott1972.ContinuousLattice.proposition_3_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:40.209804+00:00
-- url     : https://prove2.me/theorems/d0307279-c075-54e1-b930-54ab19aa08bc
-- title:
--   Continuous Lattice: proposition 3 2
-- statement:
--   **Scott 1972, Proposition 3.2.** The specialization order on `[X → Y]` is pointwise.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L127-L130
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L127-L130

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem Scott1972.ContinuousLattice.proposition_3_2 {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    (SpecializationLe f g ↔ ∀ x, SpecializationLe (f x) (g x)) := by sorry
