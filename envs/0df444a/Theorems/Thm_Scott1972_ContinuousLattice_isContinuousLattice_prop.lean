-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_isContinuousLattice_prop
-- name    : Scott1972.ContinuousLattice.isContinuousLattice_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:13.686454+00:00
-- url     : https://prove2.me/theorems/8b2ed609-e7f6-5b14-8cff-9f1bc8abbc86
-- title:
--   Continuous Lattice: is Continuous Lattice prop
-- statement:
--   The Sierpiński space `Prop` (Scott's `𝕆`) is a continuous lattice: it is a finite complete
--   lattice, so Proposition 2.8 applies.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L414-L415
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L414-L415

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.isContinuousLattice_prop : IsContinuousLattice Prop := by sorry
