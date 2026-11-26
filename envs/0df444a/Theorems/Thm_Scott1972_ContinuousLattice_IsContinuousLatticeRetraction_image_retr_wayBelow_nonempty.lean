-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_image_retr_wayBelow_nonempty
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.image_retr_wayBelow_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:09.30588+00:00
-- url     : https://prove2.me/theorems/5fdd266c-cce3-507c-aed0-97a6b5c4cfa2
-- title:
--   Is Continuous Lattice Retraction: image retr way Below nonempty
-- statement:
--   The Is Continuous Lattice Retraction construction uses the image retr way Below nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L914-L916
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L914-L916

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

theorem Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.image_retr_wayBelow_nonempty (R : IsContinuousLatticeRetraction D D') (d : D) :
    (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}).Nonempty := by sorry
