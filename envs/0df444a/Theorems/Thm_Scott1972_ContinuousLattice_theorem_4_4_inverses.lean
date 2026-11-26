-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_4_4_inverses
-- name    : Scott1972.ContinuousLattice.theorem_4_4_inverses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:59.333864+00:00
-- url     : https://prove2.me/theorems/6715542a-a0c6-43e8-933a-8b79a2cc9e60
-- title:
--   Continuous Lattice: theorem 4 4 inverses
-- statement:
--   The inverse pair Scott writes down in the proof of Theorem 4.4:
--   `i_∞ = embInfInf` and `j_∞ = projInfInf` satisfy `j_∞ ∘ i_∞ = id` and `i_∞ ∘ j_∞ = id`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L683-L686
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L683-L686

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
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

theorem Scott1972.ContinuousLattice.theorem_4_4_inverses :
    (projInfInf D₀ j₀).comp (embInfInf D₀ j₀) = ScottMap.idMap ∧
    (embInfInf D₀ j₀).comp (projInfInf D₀ j₀) = ScottMap.idMap := by sorry
