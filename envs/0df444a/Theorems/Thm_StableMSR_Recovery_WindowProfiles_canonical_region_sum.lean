-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_canonical_region_sum
-- name    : StableMSR.Recovery.WindowProfiles.canonical_region_sum
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T21:56:40.073502+00:00
-- url     : https://prove2.me/theorems/b42c8aab-d33c-456f-badc-f51022e083f5
-- title:
--   The least-point index of a label class enumerates each region exactly once
-- statement:
--   The indices of the least points of the label classes are in bijection with the nonempty regions. Consequently count and cost can both be aggregated by scanning the original point indices, with a zero contribution at every unused index.
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

theorem StableMSR.Recovery.WindowProfiles.canonical_region_sum (x : World) (u : ℕ) : (∀i∈keys x u,i< x.n ∧ piece x u i∈regions x u) ∧
    ∀{A : Type} [AddCommMonoid A] (f : Cluster x.n→A),
      (∑i∈Finset.range x.n,if i∈keys x u then f (piece x u i) else 0)=∑W∈regions x u,f W := by sorry
