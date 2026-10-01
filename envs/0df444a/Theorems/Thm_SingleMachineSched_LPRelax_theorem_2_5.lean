-- Prove2me | Theorems.Thm_SingleMachineSched_LPRelax_theorem_2_5
-- name    : SingleMachineSched.LPRelax.theorem_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T04:15:13.906311+00:00
-- url     : https://prove2.me/theorems/440ea2d1-e082-4cf6-9807-8c1fdffd4eb2
-- title:
--   Theorem 2.5 — the LP schedule's mean busy times are optimal for (R)
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j \ge 0$, indexed so that
--
--   $$\frac{w_1}{p_1} \ge \frac{w_2}{p_2} \ge \cdots \ge \frac{w_n}{p_n}.$$
--
--   Let $M^{LP}_j$ be the mean busy time of job $j$ in the LP schedule. Then $M^{LP}$ is an optimal solution to the relaxation (R):
--
--   1. $M^{LP}$ satisfies every constraint $\sum_{j \in S} p_j M^{LP}_j \ge p(S)\big(r_{\min}(S) + \tfrac12 p(S)\big)$, $\emptyset \ne S \subseteq N$;
--   2. for every feasible $M$,
--   $$\sum_{j} w_j \Big(M^{LP}_j + \tfrac12 p_j\Big) \le \sum_j w_j \Big(M_j + \tfrac12 p_j\Big).$$
--
--   Consequently $Z_R = \sum_j w_j (M^{LP}_j + \tfrac12 p_j)$.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based, and the sortedness is the hypothesis `j ≤ k → w_k/p_k ≤ w_j/p_j`. Optimality is stated for the objective of (R), $\sum_j w_j(M_j + \tfrac12 p_j)$; it differs from $\sum_j w_j M_j$ by the constant $\tfrac12\sum_j w_j p_j$, so the two forms are equivalent. The statement is made for $w_j \ge 0$ (the paper's standing assumption is $w_j > 0$).
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 173, Theorem 2.5

import Mathlib
import Definitions.Def_SingleMachineSched_LPRelax_LPSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR

namespace SingleMachineSched.LPRelax

/-- Theorem 2.5: with the jobs indexed by nonincreasing `w_j / p_j`, the mean busy time vector
`M^LP` of the LP schedule is an optimal solution to (R). -/
theorem theorem_2_5 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) :
    Shared.FeasibleR p r (mLP p r) ∧
      ∀ M : Fin n → ℝ, Shared.FeasibleR p r M → Shared.objR p w (mLP p r) ≤ Shared.objR p w M := by sorry

end SingleMachineSched.LPRelax
