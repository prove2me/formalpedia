-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_projInf_inverseLimitTopology_continuous
-- name    : Scott1972.ContinuousLattice.projInf_inverseLimitTopology_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:36.528166+00:00
-- url     : https://prove2.me/theorems/bc982388-a786-4b82-bac9-9bd4088b4a13
-- title:
--   Continuous Lattice: proj Inf inverse Limit Topology continuous
-- statement:
--   Proposition 4.2's projection `j_{∞n}` is a continuous coordinate map for the explicit
--   product/subspace inverse-limit topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L516-L519
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L516-L519

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.projInf_inverseLimitTopology_continuous (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (projInf D P n) := by sorry
