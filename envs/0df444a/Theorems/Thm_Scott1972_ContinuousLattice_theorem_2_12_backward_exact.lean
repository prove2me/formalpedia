-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_backward_exact
-- name    : Scott1972.ContinuousLattice.theorem_2_12_backward_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:43.477465+00:00
-- url     : https://prove2.me/theorems/19ed2092-3fe4-56b4-af85-bc0bb20941ab
-- title:
--   Continuous Lattice: theorem 2 12 backward exact
-- statement:
--   **Theorem 2.12, source-faithful exact-order form.** If an injective `T₀` topology on an
--   already specified complete lattice has that lattice order as its specialization order, then the
--   specified lattice is continuous and the given topology is exactly its Scott topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L317-L344
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L317-L344

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

theorem Scott1972.ContinuousLattice.theorem_2_12_backward_exact [τA : TopologicalSpace A] [T0Space A]
    (hA : IsInjectiveSpace.{u, u} A)
    (hspec : ∀ x y : A, SpecializationLe x y ↔ @LE.le A latticeA.toLE x y) :
    IsContinuousLattice A ∧
      (@scottTopologicalSpace A latticeA) = τA := by sorry
