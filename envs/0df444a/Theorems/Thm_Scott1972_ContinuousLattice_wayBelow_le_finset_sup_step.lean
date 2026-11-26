-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_le_finset_sup_step
-- name    : Scott1972.ContinuousLattice.wayBelow_le_finset_sup_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:14.256884+00:00
-- url     : https://prove2.me/theorems/4aafcc8d-e973-4368-9435-7713d4b89f27
-- title:
--   Continuous Lattice: way Below le finset sup step
-- statement:
--   **Step-function decomposition of `≪`.** If `φ ≪ g` in `[D → D']`, then `φ` lies below a finite
--   join of step functions `ē[eᵢ,eᵢ']` with `eᵢ' ≪ g eᵢ`. The finite joins of such step functions form
--   a directed family with supremum `g`, so `wayBelow_sSup_iff` produces one above `φ`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L588-L628
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L588-L628

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem Scott1972.ContinuousLattice.wayBelow_le_finset_sup_step (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    {φ g : ScottMap D D'} (h : φ ≪ g) :
    ∃ F : Finset (D × D'), (∀ p ∈ F, (p.2 : D') ≪ (g : D → D') p.1) ∧
      φ ≤ F.sup (fun p => stepMap p.1 p.2) := by sorry
