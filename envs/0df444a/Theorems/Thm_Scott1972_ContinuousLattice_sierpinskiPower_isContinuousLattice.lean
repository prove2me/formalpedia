-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_sierpinskiPower_isContinuousLattice
-- name    : Scott1972.ContinuousLattice.sierpinskiPower_isContinuousLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:54.877587+00:00
-- url     : https://prove2.me/theorems/73b57a3b-408e-5dcb-aaa1-3a2ec8dab44d
-- title:
--   Continuous Lattice: sierpinski Power is Continuous Lattice
-- statement:
--   A power of Scott's two-point space `𝕆 = Prop` is a continuous lattice: `Prop` is a continuous
--   lattice (`isContinuousLattice_prop`) and products of continuous lattices are continuous
--   (Proposition 2.9(a)). This is the order-theoretic content of "a Cartesian power of `𝕆` is a
--   continuous lattice", the construction Theorem 2.12 retracts onto.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L474-L475
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L474-L475

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.sierpinskiPower_isContinuousLattice (ι : Type*) : IsContinuousLattice (ι → Prop) := by sorry
