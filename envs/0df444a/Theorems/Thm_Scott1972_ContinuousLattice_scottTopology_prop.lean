-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottTopology_prop
-- name    : Scott1972.ContinuousLattice.scottTopology_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:55.974413+00:00
-- url     : https://prove2.me/theorems/494d9924-745b-4b07-9c84-a90aa8711b92
-- title:
--   Continuous Lattice: scott Topology prop
-- statement:
--   The Scott topology on Scott's two-point space `𝕆 = Prop` is exactly the Sierpiński topology
--   (`generateFrom {{True}}`). The Scott-open sets of `Prop` are the upper sets `∅`, `{True}`, `univ`,
--   which are precisely the Sierpiński-open sets. This is the topological identification underlying
--   Theorem 2.12: the building block `𝕆` carries its Scott topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L421-L468
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L421-L468

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.scottTopology_prop :
    (scottTopologicalSpace : TopologicalSpace Prop) = sierpinskiSpace := by sorry
