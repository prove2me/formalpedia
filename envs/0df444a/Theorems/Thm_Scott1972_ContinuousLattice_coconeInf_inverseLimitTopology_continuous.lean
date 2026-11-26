-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_inverseLimitTopology_continuous
-- name    : Scott1972.ContinuousLattice.coconeInf_inverseLimitTopology_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:59.002225+00:00
-- url     : https://prove2.me/theorems/3ea2eeeb-7d74-4384-84ae-f502415be984
-- title:
--   Continuous Lattice: cocone Inf inverse Limit Topology continuous
-- statement:
--   Corollary 4.3's formula `f∞(x) = ⨆ₙ fₙ(xₙ)` is continuous not only for the reconstructed Scott
--   topology on `D∞`, but explicitly for Scott's product/subspace inverse-limit topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L737-L742
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L737-L742

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']

theorem Scott1972.ContinuousLattice.coconeInf_inverseLimitTopology_continuous (hD : ∀ n, IsContinuousLattice (D n))
    (f : ∀ n, ScottMap (D n) D') :
    @Continuous (InverseLimit D P) D' (inverseLimitTopology D P)
      scottTopologicalSpace (coconeInf D P f) := by sorry
