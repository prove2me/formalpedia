-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_embInf_inverseLimitTopology_continuous
-- name    : Scott1972.ContinuousLattice.embInf_inverseLimitTopology_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:28.099562+00:00
-- url     : https://prove2.me/theorems/99fab505-8bac-4130-ac94-9ec0a17b15e8
-- title:
--   Continuous Lattice: emb Inf inverse Limit Topology continuous
-- statement:
--   Proposition 4.2's embedding `i_{n∞}` is also continuous for Scott's literal inverse-limit
--   topology, namely the subspace topology inherited from the product `∏ₘ Dₘ`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L508-L512
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L508-L512

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.embInf_inverseLimitTopology_continuous (hD : ∀ n, IsContinuousLattice (D n)) (n : ℕ) :
    @Continuous (D n) (InverseLimit D P) scottTopologicalSpace
      (inverseLimitTopology D P) (embInf D P n) := by sorry
