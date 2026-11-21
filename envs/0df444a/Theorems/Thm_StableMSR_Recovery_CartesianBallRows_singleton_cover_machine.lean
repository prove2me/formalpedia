-- Prove2me | Theorems.Thm_StableMSR_Recovery_CartesianBallRows_singleton_cover_machine
-- name    : StableMSR.Recovery.CartesianBallRows.singleton_cover_machine
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T20:28:29.042003+00:00
-- url     : https://prove2.me/theorems/aa5c3ff5-ad5e-47ff-b0e9-303ecca5b687
-- title:
--   A linear-time singleton cover for the diagonal case
-- statement:
--   For k=n, emit the single row whose jth center and witness are both j. Its balls cover the input and their total radius is zero. The loop takes linear charged time.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1 and Theorem 1.1. Finite deterministic RAM implementation and ball-cover certification.

import Definitions.Def_StableMSR_CartesianBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows

theorem StableMSR.Recovery.CartesianBallRows.singleton_cover_machine : ∃a : ℕ,0 < a ∧ ∃cmd : Cmd,
    ∀ (n : ℕ) (d : Point n→Point n→ℝ),1 ≤ n → IsMetricArray d →
      ∃s z,Executes d cmd (initialStore n n) s z ∧ z ≤ a*n ∧
        let x := worldOf n 1 d s
        Ready x s ∧ endpoints x ∧ ∀O,Feasible Finset.univ n O →
          ∃r < 1,good x r ∧ score x r ≤ cost d O := by
  sorry
