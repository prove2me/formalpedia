-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_bounded_width_profile_witnesses
-- name    : StableMSR.Recovery.WindowProfiles.bounded_width_profile_witnesses
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:02:20.681434+00:00
-- url     : https://prove2.me/theorems/c3086c89-6383-4c62-96f5-856d3f9b3629
-- title:
--   A bounded-width window plan supplies optimal regional endpoint witnesses at every feasible count
-- statement:
--   One bounded-size tree plan works simultaneously for all cluster counts. For each attainable count, its optimum is realized by a legal ball word whose centers and farthest witnesses lie in the region. Its cost is no greater than that of any valid window assignment with the same count.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Sections 4.1–4.4 and Appendices A.4–A.6. Exact-count combination over disjoint regions in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

theorem StableMSR.Recovery.WindowProfiles.bounded_width_profile_witnesses (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (dm : IsMetricArray x.dist) (pos : 0≤ R)
    (tw : RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) w) :
    ∃p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n), realizesWindows x W R h w p ∧
    ∀c≤ x.k,∀P : Pick x.n,valid x W R h P → number x W R P=c →
      ∃t∈TreeDP.solve x.k p,∃v : RegionalBallDP.Word,t.2.1=c ∧ Owned x W c v ∧
        RegionalBallDP.weight x c v=t.2.2 ∧ (∀j< c,∀s,∃a∈W,v j s=(a.val:ℤ)) ∧
        ∀Q : Pick x.n,valid x W R h Q → number x W R Q=c → t.2.2≤ WindowCSP.price x W R Q := by sorry
