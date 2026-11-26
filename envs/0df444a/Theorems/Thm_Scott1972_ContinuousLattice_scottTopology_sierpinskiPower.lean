-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottTopology_sierpinskiPower
-- name    : Scott1972.ContinuousLattice.scottTopology_sierpinskiPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:58.90645+00:00
-- url     : https://prove2.me/theorems/1fdca0c6-c9ee-49b8-bb54-a8b53916707f
-- title:
--   Continuous Lattice: scott Topology sierpinski Power
-- statement:
--   The Scott topology on a power `ι → 𝕆` of the Sierpiński space coincides with the product
--   (= Sierpiński power) topology. Combine Proposition 2.9(b) (the Scott topology of a product is the
--   product of the factors' Scott topologies) with `scottTopology_prop` (each factor's Scott topology
--   is the Sierpiński topology).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L481-L489
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L481-L489

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.scottTopology_sierpinskiPower (ι : Type*) :
    (scottTopologicalSpace : TopologicalSpace (ι → Prop)) =
      (inferInstance : TopologicalSpace (ι → Prop)) := by sorry
