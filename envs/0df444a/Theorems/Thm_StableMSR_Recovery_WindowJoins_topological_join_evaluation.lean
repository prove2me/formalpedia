-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_topological_join_evaluation
-- name    : StableMSR.Recovery.WindowJoins.topological_join_evaluation
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:37:54.45868+00:00
-- url     : https://prove2.me/theorems/2779cbfd-083f-4877-9cdb-dbf3abf86524
-- title:
--   A full clocked evaluation returns an optimal derivation at every designated binary root
-- statement:
--   Induct on the table clock. The update preserves the static grammar and all completed rows, and solves the next state from its lower-numbered children. The output pass copies each designated optimum into its regional index and retains the original number of scenarios.
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

theorem StableMSR.Recovery.WindowJoins.topological_join_evaluation (x : World) (hk : 0< x.k) (hn : 0< x.n) (sh : shaped x) (a : ℕ→Mem) (m : Mem)
    (init : Writes x (replace x (a 0)) seed)
    (steps : ∀i< x.rows,Writes (replace x (a i)) (replace x (a (i+1))) advance)
    (ending : Writes (replace x (a x.rows)) (replace x m) project) :
    let y:=replace x m;let g:=decode x
    storedScenes y=storedScenes x ∧ ∀r< g.size,g.goal r< g.size →
       RowOK x g (g.goal r) (0≤ center y r 0) (word y r) := by sorry
