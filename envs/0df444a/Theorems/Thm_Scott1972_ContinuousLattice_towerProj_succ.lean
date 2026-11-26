-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_towerProj_succ
-- name    : Scott1972.ContinuousLattice.towerProj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:55.374927+00:00
-- url     : https://prove2.me/theorems/5d3a4f7e-5f31-4dd0-b6c8-5a8f1defced8
-- title:
--   Continuous Lattice: tower Proj succ
-- statement:
--   The Continuous Lattice construction uses the tower Proj succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L199-L204
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L199-L204

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str

theorem Scott1972.ContinuousLattice.towerProj_succ (D₀ : CLat.{u})
    (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier)) (n : ℕ) :
    let P := towerProj D₀ j₀ n
    (towerProj D₀ j₀ (n + 1)).incl = conjMap P.incl P.retr ∧
      (towerProj D₀ j₀ (n + 1)).retr = conjMap P.retr P.incl := by sorry
