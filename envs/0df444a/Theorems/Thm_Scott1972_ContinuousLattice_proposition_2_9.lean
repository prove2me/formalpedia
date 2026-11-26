-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_9
-- name    : Scott1972.ContinuousLattice.proposition_2_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:32:14.967697+00:00
-- url     : https://prove2.me/theorems/742386bd-b70b-58e8-b0d8-6de8048f82b8
-- title:
--   Continuous Lattice: proposition 2 9
-- statement:
--   **Scott 1972, Proposition 2.9 (full statement).** The product of a family of continuous lattices
--   is again a continuous lattice (`proposition_2_9_a`) whose Scott topology agrees with the product
--   topology (`proposition_2_9_b`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L245-L250
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L245-L250

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.proposition_2_9 {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    IsContinuousLattice (∀ i, E i) ∧
      (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
        @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) := by sorry
