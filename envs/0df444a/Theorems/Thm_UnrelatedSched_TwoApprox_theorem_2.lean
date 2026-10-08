-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_theorem_2
-- name    : UnrelatedSched.TwoApprox.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:45:32.240671+00:00
-- url     : https://prove2.me/theorems/724f3059-99a8-4f5d-a0c2-d78baa169b61
-- title:
--   Theorem 2 — binary search over rounded vertices of (LP) is a 2-approximation algorithm for R||C_max
-- statement:
--   Consider the minimum makespan problem on unrelated parallel machines: $m\ge 1$ machines, $n$ jobs, and processing times $p_{ij}$ that are positive integers; let $\mathrm{OPT}$ be the minimum makespan. Fix any vertex selector $V$ (an LP solver returning, for each deadline $d\in\mathbb N$, a vertex of (LP) with $d_1=\dots=d_m=t=d$ when that LP is feasible, and 'none' otherwise). Then
--   1. an LP rounding procedure driven by $V$ exists: a decision procedure $D$ that answers 'no' exactly when $V$ does, and otherwise answers with a schedule supported on the chosen vertex that solves (IP) with $d_1=\dots=d_m=t=d$; and
--   2. for every such $D$, the schedule $\sigma_D$ output by the binary search of Lemma 1 driven by $D$ satisfies
--   $$\operatorname{makespan}(\sigma_D)\le 2\cdot\mathrm{OPT}.$$
--
--   This is the paper's main result: a polynomial algorithm for $R\,\|\,C_{\max}$ with a constant performance guarantee, where the best bound known before was $2\sqrt m$ times the optimum (Davis and Jaffe).
--
--   **Formalization Note** The paper states: "There is a 2-approximation algorithm for the minimum makespan problem on unrelated parallel machines that runs in time bounded by a polynomial in the input size." Its proof establishes that binary search (Lemma 1) over the procedure that rounds a vertex of (LP) with $d_1=\dots=d_m=t=d$ (Theorem 1) outputs a schedule of makespan at most $2\cdot\mathrm{OPT}$; this guarantee, for the algorithm as defined and for every choice of vertex by the LP solver, is what is formalized. Polynomial running time (Lemma 1's iteration count, the ellipsoid method, the rounding) is not. The output is tied to the algorithm: it is the binary search's output, and every 'almost' answer is a rounding of the LP solver's vertex, so no optimal schedule can be substituted for it.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 6, Theorem 2 (proof pp. 5–6)

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- Theorem 2, p. 6: for every vertex selector, the LP rounding procedure exists, and the binary
search of Lemma 1 driven by any such procedure outputs a schedule of makespan at most twice the
optimum. -/
theorem theorem_2 {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    (∃ D : DecisionProcedure m n, IsLPRoundingProcedure P V D) ∧
      ∀ D : DecisionProcedure m n, IsLPRoundingProcedure P V D →
        makespan (realTimes P) (binarySearch P hm D) ≤ 2 * makespan (realTimes P) σopt := by sorry

end UnrelatedSched.TwoApprox
