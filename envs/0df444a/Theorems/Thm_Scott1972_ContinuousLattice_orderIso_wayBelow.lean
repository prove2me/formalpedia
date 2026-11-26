-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_orderIso_wayBelow
-- name    : Scott1972.ContinuousLattice.orderIso_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:44.585747+00:00
-- url     : https://prove2.me/theorems/a7c4ab30-1377-516d-b452-4fdccfcf8127
-- title:
--   Continuous Lattice: order Iso way Below
-- statement:
--   Order isomorphisms preserve Scott's topological way-below relation.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L265-L272
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L265-L272

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

theorem Scott1972.ContinuousLattice.orderIso_wayBelow (e : A ≃o B) {x y : A} (h : x ≪ y) :
    e x ≪ e y := by sorry
