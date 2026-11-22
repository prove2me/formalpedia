-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_routes_cover_processed_regions
-- name    : StableMSR.Recovery.WindowProfiles.routes_cover_processed_regions
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T21:56:42.707939+00:00
-- url     : https://prove2.me/theorems/7b320592-30bb-4757-8395-3a045cc85b61
-- title:
--   Every path selects distinct local centers and covers the entire processed region prefix
-- statement:
--   Induct along the region stages. Every transition retains the old balls and appends a certified cover of the next region. A center cannot be repeated across the two sets because its representative index would have to be both strictly below and equal to the new index.
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

theorem StableMSR.Recovery.WindowProfiles.routes_cover_processed_regions (x : World) (m g : Mem) (G : Grid (replace x m) g) (u : ℕ) (hu : u< x.rows)
    (fits : ∀i< x.n,∀b≤ x.k,active (replace x m) u i b →
      Owned x (piece x u i) b (token (replace x m) u i b)) :
    ∀i< x.n,∀b≤ x.k,∀v,RegionalBallDP.Route (arena (replace x m) g) (node x.n u i b) v →
      Owned x (Finset.univ.filter (fun p=>(rep x u p).val< i+1)) b v := by sorry
