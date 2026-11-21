-- Prove2me | Theorems.Thm_StableMSR_Recovery_FewBallRows_relation_ball_certificate
-- name    : StableMSR.Recovery.FewBallRows.relation_ball_certificate
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T23:17:17.103617+00:00
-- url     : https://prove2.me/theorems/938e0a5c-1cb9-4143-b661-e4a00066c608
-- title:
--   A partition relation yields an exact-cost row of center–witness balls
-- statement:
--   The canonical decoder always returns in-range indices for a nonempty input. When the supplied relation is the equivalence relation of a feasible partition, any row containing the decoded pairs covers the instance with distinct centers and has total radius exactly equal to the partition cost. This holds for arbitrary real distance arrays.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, Branch A, Lemmas 3.3 and 3.8, and the proof of Theorem 4.5 in Appendix A. Distance-oracle implementation and certificate encoding for the Prove2Me formalization.

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem StableMSR.Recovery.FewBallRows.relation_ball_certificate (x : World) (hn : 0 < x.n) (R : Relation) :
    (∀j,∃c w : Fin x.n,pickedCenter x R j=(c.val:ℤ) ∧ pickedWitness x R j=(w.val:ℤ)) ∧
    ∀(O : Partition x.n),Feasible Finset.univ x.k O → FewBallRows.exact O R →
    ∀(m : ℕ→ℤ) (r : ℕ),encoded x (withMem x m) r R →
      good (withMem x m) r ∧ score (withMem x m) r=cost x.dist O := by
  sorry
