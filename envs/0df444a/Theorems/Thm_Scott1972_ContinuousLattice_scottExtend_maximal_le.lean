-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_maximal_le
-- name    : Scott1972.ContinuousLattice.scottExtend_maximal_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:56.182362+00:00
-- url     : https://prove2.me/theorems/40c1ad7c-e28a-4048-aa54-d83357971650
-- title:
--   Continuous Lattice: scott Extend maximal le
-- statement:
--   **Scott 1972, remark following 3.8.** `scottExtend e g` is also the maximal *sub*-solution: any
--   continuous `f'` with `f' ∘ e ⊑ g` satisfies `f' ⊑ scottExtend e g`. Same proof as
--   `scottExtend_maximal`, replacing the final equality `f' (e x) = f x` by the inequality
--   `f' (e x) ≤ g x`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L373-L382
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L373-L382

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

theorem Scott1972.ContinuousLattice.scottExtend_maximal_le (hE : IsContinuousLattice E) (e : X → Y) {g : X → E} {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (h_le : ∀ x, f' (e x) ≤ g x) (y : Y) :
    f' y ≤ scottExtend e g y := by sorry
