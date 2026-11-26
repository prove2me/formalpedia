-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_5_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.proposition_3_5_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:24.498371+00:00
-- url     : https://prove2.me/theorems/6895bd2e-647e-510c-b2b2-f9c644d57f02
-- title:
--   Continuous Lattice: proposition 3 5 preserves Directed Sup
-- statement:
--   `lambda` preserves directed suprema: both sides evaluate, pointwise at `(x, y)`, to
--   `⊔ {f (x, y) | f ∈ 𝓕}`, since suprema in every function lattice involved are pointwise.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L822-L832
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L822-L832

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

theorem Scott1972.ContinuousLattice.proposition_3_5_preservesDirectedSup :
    PreservesDirectedSup
      (scottLambda : ScottMap (D × D') D'' → ScottMap D (ScottMap D' D'')) := by sorry
