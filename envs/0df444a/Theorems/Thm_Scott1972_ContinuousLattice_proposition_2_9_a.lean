-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_9_a
-- name    : Scott1972.ContinuousLattice.proposition_2_9_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:11.883037+00:00
-- url     : https://prove2.me/theorems/d266d4e0-e79c-5ca8-a707-400e0f5bf428
-- title:
--   Continuous Lattice: proposition 2 9 a
-- statement:
--   **Scott 1972, Proposition 2.9(a) (order-theoretic content).** The Cartesian product of any
--   family of continuous lattices is a continuous lattice. (Part (b), that the induced topology of
--   the product agrees with the product topology, is `proposition_2_9_b` below; `proposition_2_9`
--   bundles the two.)
--
--   The key step is that if `a ≪ yᵢ` in the factor `Dᵢ`, then the cylinder element `[a]ⁱ`
--   (equal to `a` in coordinate `i` and `⊥` elsewhere) is way below `y` in the product: the
--   preimage `{z | zᵢ ∈ U}` of a Scott-open witness `U ⊆ Dᵢ` is Scott-open in the product
--   (suprema are computed coordinatewise). Any upper bound `b` of `{x | x ≪ y}` therefore
--   dominates every `[a]ⁱ`, so `a = ([a]ⁱ)ᵢ ≤ bᵢ`; ranging over `a ≪ yᵢ` and using continuity of
--   `Dᵢ` gives `yᵢ ≤ bᵢ` for all `i`, i.e. `y ≤ b`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L69-L101
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L69-L101

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.proposition_2_9_a {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) : IsContinuousLattice (∀ i, E i) := by sorry
