-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_forward
-- name    : Scott1972.ContinuousLattice.theorem_2_12_forward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:58.573164+00:00
-- url     : https://prove2.me/theorems/f30b9162-daeb-55f5-aa5f-4661f10e1650
-- title:
--   Continuous Lattice: theorem 2 12 forward
-- statement:
--   **Scott 1972, Theorem 2.12 (forward direction).** Every continuous lattice is an injective
--   space under its Scott topology. This is the substantial half of the equivalence "injective
--   spaces = continuous lattices", and is exactly Proposition 2.11.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L494-L496
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L494-L496

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.theorem_2_12_forward {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace := by sorry
