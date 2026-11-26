-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_9_b
-- name    : Scott1972.ContinuousLattice.proposition_2_9_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:17.38477+00:00
-- url     : https://prove2.me/theorems/420c4fac-95ec-5a46-868a-c43c773d4efe
-- title:
--   Continuous Lattice: proposition 2 9 b
-- statement:
--   **Scott 1972, Proposition 2.9(b).** For a family of continuous lattices, the Scott topology of
--   the product coincides with the product of the Scott topologies of the factors.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L199-L240
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L199-L240

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.proposition_2_9_b {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
      @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) := by sorry
