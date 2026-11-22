-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_local_profiles_certify_exact_count_search
-- name    : StableMSR.Recovery.WindowProfiles.local_profiles_certify_exact_count_search
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T21:56:56.003912+00:00
-- url     : https://prove2.me/theorems/aed6f316-590a-405d-afb1-d1f418774fe2
-- title:
--   Independent bounded-width regional profiles certify a globally feasible exact-count terminal
-- statement:
--   For a witnessing set of window assignments, choose its count at the canonical stage of each region. Every feasible path to the final count covers the entire universe with distinct centers. The comparison path using those counts costs at most the sum of the assignment costs. The shortest-path decoder can therefore choose its own allocation.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Sections 4.1–4.4 and Appendices A.4–A.6. Exact-count combination over disjoint regions in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

theorem StableMSR.Recovery.WindowProfiles.local_profiles_certify_exact_count_search (x : World) (e : ℚ) (m g : Mem) (hn : 0< x.n) (ok : Profiles x e m) (G : Grid (replace x m) g)
    (u : ℕ) (hu : u< x.rows) (pos : 0< scale x u)
    (tw : ∀W∈regions x u,RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist (scale x u) W) (widthBound (e:ℝ)))
    (P : Cluster x.n→Pick x.n) (validP : ∀W∈regions x u,valid x W (scale x u) (budget (e:ℝ)) (P W))
    (total : (∑W∈regions x u,number x W (scale x u) (P W))=x.k) :
    let y:=arena (replace x m) g
    let r:=node x.n u (x.n-1) x.k
    RegionalBallDP.vertex y r ∧ RegionalBallDP.InTable y r ∧
      ∃v,RegionalBallDP.Route y r v ∧ RegionalBallDP.weight y x.k v≤∑W∈regions x u,WindowCSP.price x W (scale x u) (P W) := by sorry
