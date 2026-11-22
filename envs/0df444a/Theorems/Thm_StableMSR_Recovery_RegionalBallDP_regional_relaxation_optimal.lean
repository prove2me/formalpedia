-- Prove2me | Theorems.Thm_StableMSR_Recovery_RegionalBallDP_regional_relaxation_optimal
-- name    : StableMSR.Recovery.RegionalBallDP.regional_relaxation_optimal
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T13:12:41.877987+00:00
-- url     : https://prove2.me/theorems/da06c00d-9936-425a-8f00-8b969c22bc2c
-- title:
--   Exact minimum with a reconstructible ball word for every reachable regional state
-- statement:
--   Every reachable state yields an actual concatenation of regional ball choices with minimum true sum of radii at its exact prefix width. The proof tracks predecessor witnesses, proves that replacing a prefix by its minimum preserves the appended cost, and bounds the required rounds by the number of rows. All output endpoints are legal even on unused rows.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission.

import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.RegionalBallDP.regional_relaxation_optimal (x : World) (hk : 0<x.k) (hn : 0<x.n) (hs : shape x)
    (h : ℕ→ℕ→ℤ) (a : Writes x (withMem x (h 0)) seedTable)
    (b : ∀i<x.rows,Writes (withMem x (h i)) (withMem x (h (i+1))) tick)
    (m : ℕ→ℤ) (c : Writes (withMem x (h x.rows)) (withMem x m) clean) :
    endpoints (withMem x m) ∧ ∀v,vertex x v → ∀u,Route x v u →
      Route x v (word (withMem x m) v) ∧
      weight x (width x v) (word (withMem x m) v) ≤ weight x (width x v) u := by
  sorry
