-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_orderIso_wayBelow_iff
-- name    : Scott1972.ContinuousLattice.orderIso_wayBelow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:48.983361+00:00
-- url     : https://prove2.me/theorems/ee1031c9-55fe-5245-a54e-506614df7f6c
-- title:
--   Continuous Lattice: order Iso way Below iff
-- statement:
--   Scott's topological way-below relation is invariant under order isomorphism.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L275-L278
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L275-L278

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

theorem Scott1972.ContinuousLattice.orderIso_wayBelow_iff (e : A ≃o B) {x y : A} :
    x ≪ y ↔ e x ≪ e y := by sorry
