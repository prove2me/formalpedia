-- Prove2me | Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_cheapest_cover_recovers
-- name    : StableMSR.Recovery.BallCoverCatalog.cheapest_cover_recovers
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T20:24:02.233633+00:00
-- url     : https://prove2.me/theorems/ed9bca52-6195-43b2-83df-643ac066e7f0
-- title:
--   A covering ball certificate suffices for unique optimal recovery
-- statement:
--   Choose the lowest-score valid row, assign centers to their own clusters, and assign every other point to its first covering ball. The decoded partition is feasible and its actual cost is bounded by the row score. A stable optimum is recovered whenever a row has score at most its cost.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_BallCoverCatalog
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open StableMSR.Recovery.BallCoverCatalog

theorem StableMSR.Recovery.BallCoverCatalog.cheapest_cover_recovers (x : World) (s : MinSumFPT.State) (hk : 1 ≤ x.k) (hn : x.k ≤ x.n)
    (hm : IsMetricArray x.dist) (he : endpoints x)
    (hs : ∀i < x.n,s.imem (-1-(i:ℤ))=output x i) :
    ValidLabels x.n x.k s ∧ ∀ (γ : ℝ),1 ≤ γ → ∀ O,Stable x.dist x.k γ O →
      (∃r < x.rows,good x r ∧ score x r ≤ cost x.dist O) → outputPartition x.n x.k s=O := by
  sorry
