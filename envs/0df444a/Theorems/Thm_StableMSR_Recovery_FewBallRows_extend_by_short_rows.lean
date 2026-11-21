-- Prove2me | Theorems.Thm_StableMSR_Recovery_FewBallRows_extend_by_short_rows
-- name    : StableMSR.Recovery.FewBallRows.extend_by_short_rows
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T23:17:47.611692+00:00
-- url     : https://prove2.me/theorems/303ae377-75b1-417d-a429-aadfb87897fc
-- title:
--   Append all bounded-width descriptions to an arbitrary ball table
-- statement:
--   Starting from any initialized table, a deterministic distance-RAM command preserves its rows and appends every word of $2(h+1)$ base-$n$ digits in the fixed ball-row layout. The work is bounded by a single polynomial in the dimensions and the number of appended words, independently of $h$.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, Branch A, Lemmas 3.3 and 3.8, and the proof of Theorem 4.5 in Appendix A. Distance-oracle implementation and certificate encoding for the Prove2Me formalization.

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem StableMSR.Recovery.FewBallRows.extend_by_short_rows : ∃p : Polynomial ℕ,∀h : ℕ,∃cmd : Cmd,∀(x : World) (s : Store),
    0 < x.n → h < x.k → x.k ≤ x.n → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval (x.cap + rows x.n (h+1)) ∧
    let y := worldOf x.k (x.rows + rows x.n (h+1)) x.dist t
    Ready y t ∧ y.mem 1=(h:ℤ) ∧ y.mem 2=(x.rows:ℤ) ∧
    (∀r < x.rows,∀j < x.k,center y r j=center x r j ∧ witness y r j=witness x r j) ∧
    (∀u < rows x.n (h+1),∀j ≤ h,center y (x.rows+u) j=(digit x.n u (2*j):ℤ) ∧
      witness y (x.rows+u) j=(digit x.n u (2*j+1):ℤ)) := by
  sorry
