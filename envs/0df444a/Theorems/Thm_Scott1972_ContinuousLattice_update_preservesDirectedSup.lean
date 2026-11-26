-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_update_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.update_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:42.477468+00:00
-- url     : https://prove2.me/theorems/0cfb709a-3d2c-463e-9c81-fe8a9e0cc74c
-- title:
--   Continuous Lattice: update preserves Directed Sup
-- statement:
--   Plugging a value into a fixed coordinate, `v ↦ Function.update z i v`, preserves directed
--   suprema: away from `i` the result is the constant `z j`, and at `i` it is the identity.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L122-L137
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L122-L137

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.update_preservesDirectedSup {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, CompleteLattice (E i)] (z : ∀ i, E i) (i : ι) :
    PreservesDirectedSup (fun v : E i => Function.update z i v) := by sorry
