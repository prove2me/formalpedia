-- Prove2me | Theorems.Thm_StableMSR_Recovery_feasible_fallback_program
-- name    : StableMSR.Recovery.feasible_fallback_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T14:48:03.085127+00:00
-- url     : https://prove2.me/theorems/575018d6-52ce-4fff-a216-6ae4b44c0141
-- title:
--   Algorithm 1 initialization: an exact-k partition in 5n+12 interpreter steps
-- statement:
--   There is one finite deterministic program $P$, independent of all input data, that initializes a feasible clustering on every input with $1\le k\le n$. At exactly
--   $$t=5n+12$$
--   steps of the canonical interpreter, its state has halted, has charged exactly $5n+12$ units of work, and contains validated surjective labels whose decoded fibers form a feasible partition into exactly $k$ nonempty clusters. The distance array can be arbitrary: metricity and stability are not required.
--
--   This implements the feasible-answer initialization in Algorithm 1. It includes $k=1$, $k=n$, and $n=k=1$. It supplies initialization only and does not assert recovery of the optimum for general $k$.
--
--   **Formalization Note.** The program is selected before $n,k,d$, and the result concerns actual `execute` states and charged work in the existing machine model.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Algorithm 1, line 1; Appendix A.5 (every returned answer is feasible). The exact 20-instruction implementation and 5n+12 count refine the source's feasible initialization step.

import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

theorem feasible_fallback_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ), 1 ≤ k → k ≤ n →
        let s := execute P n k d (5*n+12)
        s.halted = true ∧ s.work = 5*n+12 ∧ ValidLabels n k s ∧
          Feasible Finset.univ k (outputPartition n k s) := by sorry

end StableMSR.Recovery
