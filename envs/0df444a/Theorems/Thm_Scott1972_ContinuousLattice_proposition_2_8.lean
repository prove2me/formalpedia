-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_8
-- name    : Scott1972.ContinuousLattice.proposition_2_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:48.541448+00:00
-- url     : https://prove2.me/theorems/fc854944-38f3-4c81-8d51-f2547fa44ea6
-- title:
--   Continuous Lattice: proposition 2 8
-- statement:
--   **Scott 1972, Proposition 2.8.** A finite lattice is a continuous lattice. In a finite
--   lattice every principal up-set `Set.Ici y` is Scott-open (a non-empty directed set is finite,
--   so it attains its supremum), hence `y ≪ y`; therefore `y` is the supremum of `{x | x ≪ y}`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L50-L56
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L50-L56

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.proposition_2_8 [Finite D] : IsContinuousLattice D := by sorry
