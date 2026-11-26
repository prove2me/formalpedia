-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_4_4
-- name    : Scott1972.ContinuousLattice.theorem_4_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:53.364074+00:00
-- url     : https://prove2.me/theorems/52bb9af3-5ba0-5093-840f-f565f82264c1
-- title:
--   Continuous Lattice: theorem 4 4
-- statement:
--   **Scott 1972, Theorem 4.4** (`sources/ScottContinLatt1972.md`):
--   *The inverse limit \(D_\infty\) of the recursively defined sequence
--   \(\langle D_n, j_n \rangle_{n=0}^{\infty}\) of function spaces is not only a
--   continuous lattice, but it is also homeomorphic to its own function space
--   \([D_\infty \to D_\infty]\).*  Here “inverse limit” carries Scott's subspace
--   topology from the Pi product, while the function space carries Definition 3.1's
--   pointwise/Pi-induced topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L736-L748
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L736-L748

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

theorem Scott1972.ContinuousLattice.theorem_4_4 (h₀ : IsContinuousLattice D₀.carrier) :
    @IsContinuousLattice (DInf D₀ j₀) inferInstance ∧
      Nonempty
        (@Homeomorph (DInf D₀ j₀) (DInfFn D₀ j₀)
          (inverseLimitTopology (towerType D₀) (towerProj D₀ j₀))
          (scottMapInducedPiTopology (DInf D₀ j₀) (DInf D₀ j₀))) := by sorry
