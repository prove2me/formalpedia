-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_projInfInf_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.projInfInf_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:00.126597+00:00
-- url     : https://prove2.me/theorems/f2c9eaa9-fca0-4c73-a5e1-5aad3e047352
-- title:
--   Continuous Lattice: proj Inf Inf preserves Directed Sup
-- statement:
--   `j_∞` is Scott-continuous (it is a bundled `ScottMap`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L316-L318
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L316-L318

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

theorem Scott1972.ContinuousLattice.projInfInf_preservesDirectedSup :
    PreservesDirectedSup (projInfInf D₀ j₀ : DInfFn D₀ j₀ → DInf D₀ j₀) := by sorry
