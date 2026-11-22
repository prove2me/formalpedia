-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_derived_endpoint_bounds
-- name    : StableMSR.Recovery.WindowJoins.derived_endpoint_bounds
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:37:57.734013+00:00
-- url     : https://prove2.me/theorems/56d392fa-f912-4581-98f2-2d357b36275a
-- title:
--   Every binary derivation has legal endpoints and zero padding
-- statement:
--   Literal endpoint rows are range-checked. At binary joins each occupied slot belongs to exactly one child, and all slots past the declared row length are zero.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.6 (tree-decomposition dynamic programming over regional windows), in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

theorem StableMSR.Recovery.WindowJoins.derived_endpoint_bounds (x : World) (g : Rules) (s : Sane x g) (hn : 0< x.n) (v : ℕ) (u : Word) (d : Derives x.k g v u) :
    (∀j w,0≤ u j w ∧ u j w<(x.n:ℤ)) ∧ ∀j,g.len v≤ j → ∀w,u j w=0 := by sorry
