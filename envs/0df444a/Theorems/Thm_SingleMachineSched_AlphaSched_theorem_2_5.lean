-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_theorem_2_5
-- name    : SingleMachineSched.AlphaSched.theorem_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:27.619687+00:00
-- url     : https://prove2.me/theorems/4e8b30b6-6260-4534-9d24-3fbcf93b72fd
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
--   Consequently $Z_R = \sum_j w_j (M^{LP}_j + \tfrac12 p_j)$, the bound against which the α-schedule's expected cost is measured.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based, and the sortedness is the hypothesis `j ≤ k → w_k/p_k ≤ w_j/p_j`. This restates Theorem 2.5 of the paper inside this mission (it is also a milestone of the companion mission on the LP relaxations, which is not yet published).
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 173, Theorem 2.5

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_LPSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR

namespace SingleMachineSched.AlphaSched

/-- Theorem 2.5 (Goemans et al. 2002, p. 173): with the jobs indexed by nonincreasing
`w_j / p_j`, the mean busy time vector `M^LP` of the LP schedule is an optimal solution to (R). -/
theorem theorem_2_5 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) :
    Shared.FeasibleR p r (mLP p r) ∧
      ∀ M : Fin n → ℝ, Shared.FeasibleR p r M → Shared.objR p w (mLP p r) ≤ Shared.objR p w M := by sorry

end SingleMachineSched.AlphaSched
