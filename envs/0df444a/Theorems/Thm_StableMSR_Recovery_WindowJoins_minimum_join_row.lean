-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_minimum_join_row
-- name    : StableMSR.Recovery.WindowJoins.minimum_join_row
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:38:08.46621+00:00
-- url     : https://prove2.me/theorems/d37c4d24-6a3a-414d-bde0-14ea01644170
-- title:
--   A binary relaxation preserves all feasible exact-count witnesses and their minimum cost
-- statement:
--   Assuming lower-numbered states have their optimum witnesses, selecting the least cheapest eligible production yields an optimum at the current state. A missing production gives an unreachable state, and equal-cost alternatives are resolved deterministically.
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

theorem StableMSR.Recovery.WindowJoins.minimum_join_row (x : World) (g : Rules) (on : ℕ→Prop) (T : ℕ→Word) (v : ℕ)
    (hn : 0< x.n) (s : Sane x g) (size : g.size≤ x.rows) (prev : ∀p< v,RowOK x g p (on p) (T p)) :
    let B:=bestWord x g on T v
    RowOK x g v (0≤ B 0 false) (fun j w=>if j< x.k then B j w else 0) := by sorry
