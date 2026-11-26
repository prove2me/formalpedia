-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_sierpinski_backward
-- name    : Scott1972.ContinuousLattice.theorem_2_12_sierpinski_backward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:32:32.407839+00:00
-- url     : https://prove2.me/theorems/c0a6aa1b-ed8b-5c31-bc0b-9e5d0a086eba
-- title:
--   Continuous Lattice: theorem 2 12 sierpinski backward
-- statement:
--   **Scott 1972, Theorem 2.12 (backward, Sierpiński base case).** `Prop` is a continuous
--   lattice (`isContinuousLattice_prop`), so its injectivity (Proposition 1.2) is an instance of the
--   equivalence.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L501-L502
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L501-L502

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.theorem_2_12_sierpinski_backward (_h : IsContinuousLattice Prop) : IsInjectiveSpace Prop := by sorry
