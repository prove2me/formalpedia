-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_11
-- name    : Scott1972.ContinuousLattice.proposition_2_11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:00.573438+00:00
-- url     : https://prove2.me/theorems/7f6c9562-b957-47c0-ae37-b6bc902d765d
-- title:
--   Continuous Lattice: proposition 2 11
-- statement:
--   **Scott 1972, Proposition 2.11.** Every continuous lattice is an injective space under its
--   induced (Scott) topology. The witness is `scottExtend`, which extends any continuous `f` along
--   any embedding `e` (`scottExtend_eq_of_continuous`) and is itself continuous
--   (`scottExtend_continuous`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L405-L410
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L405-L410

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.proposition_2_11 {E : Type*} [CompleteLattice E] (hE : IsContinuousLattice E) :
    @IsInjectiveSpace E scottTopologicalSpace := by sorry
