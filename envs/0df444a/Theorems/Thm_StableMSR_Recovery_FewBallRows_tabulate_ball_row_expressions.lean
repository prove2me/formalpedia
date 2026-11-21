-- Prove2me | Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
-- name    : StableMSR.Recovery.FewBallRows.tabulate_ball_row_expressions
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-20T23:18:12.488863+00:00
-- url     : https://prove2.me/theorems/88dac7be-92f5-4745-8ff4-718d3b3cd7ec
-- title:
--   Uniform two-pass tabulation of oracle rows
-- statement:
--   Two bounded oracle expressions describe the center and witness entries of a rectangular table. A deterministic command computes all entries from the original integer memory, then installs the completed table. This allows the expressions to read any input row, including one whose output has already been calculated.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, Branch A, Lemmas 3.3 and 3.8, and the proof of Theorem 4.5 in Appendix A. Distance-oracle implementation and certificate encoding for the Prove2Me formalization.

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem StableMSR.Recovery.FewBallRows.tabulate_ball_row_expressions (f : World→ℕ→ℕ→Bool→ℤ)
    (hf : ∀w : Bool,Form (fun x ρ=>iv (f x (ρ 0) (ρ 1) w))) :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store), Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval x.cap ∧
      let y := worldOf x.k x.rows x.dist t
      Ready y t ∧ ∀r < x.rows,∀j < x.k,center y r j=f x r j false ∧ witness y r j=f x r j true := by
  sorry
