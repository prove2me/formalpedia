-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_sSupMaps_apply
-- name    : Scott1972.ContinuousLattice.ScottMap.sSupMaps_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:54.941511+00:00
-- url     : https://prove2.me/theorems/83bf59ba-b0c2-4237-b7b2-c32203301d5e
-- title:
--   Scott Map: s Sup Maps apply
-- statement:
--   The Scott Map construction uses the s Sup Maps apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L266-L269
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L266-L269

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
open Scott1972.ContinuousLattice.ScottMap

theorem Scott1972.ContinuousLattice.ScottMap.sSupMaps_apply (F : Set (ScottMap D D')) (x : D) :
    (sSupMaps F : D → D') x =
      sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F) := by sorry
