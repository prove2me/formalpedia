-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCSP_catalog_to_local_trials
-- name    : StableMSR.Recovery.WindowCSP.catalog_to_local_trials
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T16:03:57.167806+00:00
-- url     : https://prove2.me/theorems/45b02ec0-e1ad-4f01-a562-5f9d4722bce3
-- title:
--   A uniform polynomial distance-RAM converts ball-cover rows into single-edge regional trials
-- statement:
--   Resize the oracle table, retain the old row count, and materialize one edge from the empty root to a full-width state for each old row. A feasible row supplies distinct centers and covers every input point. Its exact sum of radii is the edge cost. The construction has one command and polynomial overhead for all input sizes and all row counts.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Lemmas 3.3, 3.8, 3.9(iii), 4.4, Proposition 4.2, Algorithm 1, and Appendix A.4–A.6. Alternative pairwise formulation using bounded-overlap window traces in the mission’s real-distance model.

import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.WindowCSP.catalog_to_local_trials :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0<x.k → Ready x s → endpoints x →
    ∃t z,Executes x.dist cmd s t z ∧ z≤p.eval x.cap ∧
      let y:=worldOf x.k (1+4*(x.rows+1)) x.dist t
      Ready y t ∧ RegionalBallDP.shape y ∧ ∀r<x.rows, good x r → ∀B : ℝ,score x r≤B →
        Nonempty (RegionalBallDP.LocalTrial y (r+2) B) := by
  sorry
