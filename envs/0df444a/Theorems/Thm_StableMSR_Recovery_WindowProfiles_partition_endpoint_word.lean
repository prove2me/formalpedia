-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_partition_endpoint_word
-- name    : StableMSR.Recovery.WindowProfiles.partition_endpoint_word
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:02:27.635829+00:00
-- url     : https://prove2.me/theorems/a6ea9c12-18b5-442d-ad4e-f8f2b3ac51a4
-- title:
--   Every exact regional partition has an owned endpoint word of the same radius sum
-- statement:
--   For every block choose a center attaining the discrete radius and a farthest member serving as its radius witness. Enumerating the blocks gives distinct centers, coverage of the region, legal endpoints in the region and exact equality of costs. Empty regions and zero counts are included.
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

theorem StableMSR.Recovery.WindowProfiles.partition_endpoint_word (x : World) (W : Cluster x.n) (c : ℕ) (Q : Partition x.n) (hc : c≤ x.k) (feas : Feasible W c Q) :
    ∃v : RegionalBallDP.Word,Owned x W c v ∧ RegionalBallDP.weight x c v=cost x.dist Q ∧
      ∀j< c,∀s,∃p∈W,v j s=(p.val:ℤ) := by sorry
