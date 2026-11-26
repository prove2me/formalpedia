-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_sSup_image_retr_wayBelow
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.sSup_image_retr_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:22.986309+00:00
-- url     : https://prove2.me/theorems/f5f14555-299a-5278-9252-f37efefb0571
-- title:
--   Is Continuous Lattice Retraction: s Sup image retr way Below
-- statement:
--   For `d` in the retract, the ambient way-below set of `i(d)` pushed back by `j` is a directed
--   family whose supremum (computed in `D`) is `d`. This is the identity `j(⊔S′) = ⊔S` applied to
--   `S = {j(x') : x' ≪ i(d)}`, combined with continuity of `D'`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L907-L912
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L907-L912

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
open Scott1972.ContinuousLattice.IsContinuousLatticeRetraction

theorem Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.sSup_image_retr_wayBelow (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') (d : D) :
    sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) = d := by sorry
