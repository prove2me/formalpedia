-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_join_outputs_are_profiles
-- name    : StableMSR.Recovery.WindowJoins.join_outputs_are_profiles
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:38:03.164064+00:00
-- url     : https://prove2.me/theorems/c4704786-3f05-4afc-95cf-c15ecba763d7
-- title:
--   Projected optimal binary derivations satisfy the full regional profile contract
-- statement:
--   At each output index, every reachable root is a sound regional cover. The minimum derivation is as cheap as every represented window assignment, and the empty padding states remain available. Range checking preserves all occupied endpoint slots.
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

theorem StableMSR.Recovery.WindowJoins.join_outputs_are_profiles (x : World) (e : ℚ) (H : ℕ) (m out : Mem) (hn : 0< x.n) (hk : 0< x.k)
    (cert : Encodes x e {x with rows:=H,mem:=m})
    (ok : let y:={x with rows:=H,mem:=m};let z:={y with mem:=out};let g:=decode y
          ∀r< g.size,g.goal r< g.size → RowOK y g (g.goal r) (0≤ center z r 0) (word z r)) :
    Profiles x e out := by sorry
