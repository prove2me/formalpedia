-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_scottTopology_eq_induced_pi
-- name    : Scott1972.ContinuousLattice.inverseLimit_scottTopology_eq_induced_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:43.524312+00:00
-- url     : https://prove2.me/theorems/68187fe7-fc0d-43b4-ac0b-cd0792e35fac
-- title:
--   Continuous Lattice: inverse Limit scott Topology eq induced pi
-- statement:
--   The Scott lattice topology constructed on `D∞` agrees with Scott's literal inverse-limit
--   topology: the subspace topology inherited from the Pi product of the stage Scott topologies.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L281-L287
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L281-L287

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.inverseLimit_scottTopology_eq_induced_pi (hD : ∀ n, IsContinuousLattice (D n)) :
    (scottTopologicalSpace : TopologicalSpace (InverseLimit D P)) =
      inverseLimitTopology D P := by sorry
