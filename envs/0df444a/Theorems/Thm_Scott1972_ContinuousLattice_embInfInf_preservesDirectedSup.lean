-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_embInfInf_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.embInfInf_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:57.224445+00:00
-- url     : https://prove2.me/theorems/e7b3235b-70b1-428e-8b3d-fbef05859b12
-- title:
--   Continuous Lattice: emb Inf Inf preserves Directed Sup
-- statement:
--   `i_∞` is Scott-continuous (it is a bundled `ScottMap`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L311-L313
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L311-L313

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

theorem Scott1972.ContinuousLattice.embInfInf_preservesDirectedSup :
    PreservesDirectedSup (embInfInf D₀ j₀ : DInf D₀ j₀ → DInfFn D₀ j₀) := by sorry
