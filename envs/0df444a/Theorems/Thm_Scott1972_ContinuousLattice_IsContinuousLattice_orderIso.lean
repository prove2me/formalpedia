-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_orderIso
-- name    : Scott1972.ContinuousLattice.IsContinuousLattice.orderIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:15.033471+00:00
-- url     : https://prove2.me/theorems/778f247d-606c-40ac-bf67-0a21881a2020
-- title:
--   Is Continuous Lattice: order Iso
-- statement:
--   Continuous-lattice structure transfers across an order isomorphism.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L281-L290
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L281-L290

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

theorem Scott1972.ContinuousLattice.IsContinuousLattice.orderIso (e : A ≃o B) (hB : IsContinuousLattice B) :
    IsContinuousLattice A := by sorry
