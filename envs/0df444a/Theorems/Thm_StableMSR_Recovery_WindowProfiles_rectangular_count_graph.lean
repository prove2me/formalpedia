-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowProfiles_rectangular_count_graph
-- name    : StableMSR.Recovery.WindowProfiles.rectangular_count_graph
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:00:17.362595+00:00
-- url     : https://prove2.me/theorems/b8b75a90-a94d-4086-9f2b-da27dd6fefd3
-- title:
--   The rectangular table has exactly the prescribed count transitions and shifted local witnesses
-- statement:
--   Decode the block of each row and the digits of each transition index. The inverse decoding excludes every unintended incoming edge. Legal transitions link consecutive region stages, preserve the preceding center slots, and append the local endpoints at the exact count offset.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Sections 4.1–4.4 and Appendices A.4–A.6. Exact-count combination over disjoint regions in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowProfilePacking
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

theorem StableMSR.Recovery.WindowProfiles.rectangular_count_graph (x : World) (hk : 1≤ x.k) (hn : x.k< x.n) (m : Mem)
    (tab : ∀r< height x,∀j< x.k,∀w,RegionalBallDP.field (arena x m) r j w=
      packed ({x with rows:=height x,mem:=Function.update x.mem 0 (x.rows:ℤ)}) r j w) : Grid x m := by sorry
