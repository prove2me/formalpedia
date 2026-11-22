-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_exact_count_routes_add_costs
-- name    : StableMSR.Recovery.WindowProfiles.exact_count_routes_add_costs
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T21:56:51.772816+00:00
-- url     : https://prove2.me/theorems/639eb22d-2fa3-4155-8b96-330df28b5527
-- title:
--   An arbitrary allocation of local counts has a path with exactly the sum of its ball costs
-- statement:
--   Use successive partial sums of the desired local counts as the states of one path. The global ball word concatenates the local words at these offsets, so the oracle radius sum is exactly additive, including at zero-count stages.
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

theorem StableMSR.Recovery.WindowProfiles.exact_count_routes_add_costs (x : World) (g : Mem) (G : Grid x g) (u : ℕ) (hu : u< x.rows) (hn : 0< x.n) (d : ℕ→ℕ)
    (total : (∑i∈Finset.range x.n,d i)=x.k) (act : ∀i< x.n,active x u i (d i)) :
    ∃v,RegionalBallDP.Route (arena x g) (node x.n u (x.n-1) x.k) v ∧
      RegionalBallDP.weight x x.k v=∑i∈Finset.range x.n,RegionalBallDP.weight x (d i) (token x u i (d i)) := by sorry
