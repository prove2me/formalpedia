-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_proj
-- name    : Scott1972.ContinuousLattice.wayBelow_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:37.893589+00:00
-- url     : https://prove2.me/theorems/ef026030-84eb-5ae4-a9ac-0f85b16151d3
-- title:
--   Continuous Lattice: way Below proj
-- statement:
--   A way-below relation in a product projects to each coordinate: if `a ≪ z` in `∏ᵢ Eᵢ` then
--   `aᵢ ≪ zᵢ`. The witnessing Scott-open neighbourhood of `zᵢ` is the preimage of a product Scott-open
--   witness under `v ↦ Function.update z i v`, which is Scott-open by `update_preservesDirectedSup`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L142-L153
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L142-L153

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.wayBelow_proj {ι : Type*} {E : ι → Type*} [∀ i, CompleteLattice (E i)]
    {a z : ∀ i, E i} (h : a ≪ z) (i : ι) : a i ≪ z i := by sorry
