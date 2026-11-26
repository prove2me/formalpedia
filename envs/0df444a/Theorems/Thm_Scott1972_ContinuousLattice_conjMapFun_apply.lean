-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_conjMapFun_apply
-- name    : Scott1972.ContinuousLattice.conjMapFun_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:44.613965+00:00
-- url     : https://prove2.me/theorems/85dfc2eb-2b7d-47ab-a820-2b82e227ae25
-- title:
--   Continuous Lattice: conj Map Fun apply
-- statement:
--   The Continuous Lattice construction uses the conj Map Fun apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L83-L84
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L83-L84

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
open Set
variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]

theorem Scott1972.ContinuousLattice.conjMapFun_apply (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) (x : W) :
    conjMapFun post pre f x = post (f (pre x)) := by sorry
