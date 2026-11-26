-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_towerType_succ
-- name    : Scott1972.ContinuousLattice.towerType_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:55.387156+00:00
-- url     : https://prove2.me/theorems/3503fec4-9cec-4c4e-9a99-0e8587c080a6
-- title:
--   Continuous Lattice: tower Type succ
-- statement:
--   `D_{n+1}` is *definitionally* the function space `[Dₙ → Dₙ]`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L52-L53
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L52-L53

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str

theorem Scott1972.ContinuousLattice.towerType_succ (D₀ : CLat.{u}) (n : ℕ) :
    towerType D₀ (n + 1) = ScottMap (towerType D₀ n) (towerType D₀ n) := by sorry
