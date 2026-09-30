-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_theorem_2_5
-- name    : SingleMachineSched.AlphaJSched.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:49.250985+00:00
-- url     : https://prove2.me/theorems/ef544564-b1ea-4f7c-bf61-ea1808b25eb2
-- title:
--   Theorem 2.5 — the LP schedule's mean busy times solve (R)
-- statement:
--   Let $n$ jobs have integral processing times $p_j>0$, integral release dates $r_j\ge0$ and weights $w_j\ge0$, indexed so that $w_0/p_0\ge w_1/p_1\ge\dots\ge w_{n-1}/p_{n-1}$. Let $M^{LP}_j$ be the mean busy time of job $j$ in the LP schedule. Then $M^{LP}$ is an optimal solution of the mean busy time relaxation (R):
--
--   1. $M^{LP}$ is feasible for (R): $\displaystyle\sum_{j\in S}p_jM^{LP}_j\ge p(S)\bigl(r_{\min}(S)+\tfrac12p(S)\bigr)$ for every nonempty set $S$ of jobs;
--   2. for every feasible $M$,
--   $$\sum_{j}w_j\Bigl(M^{LP}_j+\tfrac12p_j\Bigr)\ \le\ \sum_j w_j\Bigl(M_j+\tfrac12p_j\Bigr).$$
--
--   In particular $Z_R=\sum_j w_j(M^{LP}_j+\tfrac12p_j)$, which is the form in which the result enters the proof of Theorem 3.9.
--
--   **Formalization Note.** The paper's standing assumption is $w_j>0$; the statement is made for $w_j\ge0$, the range of Corollary 2.6, which is a stronger claim and specializes to the paper's. This restates Theorem 2.5 of the first mission of this series (not yet published) in this mission's namespace.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 173, Theorem 2.5

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR

namespace SingleMachineSched.AlphaJSched

/-- Theorem 2.5: with the jobs indexed by nonincreasing `w_j / p_j`, the mean busy time vector
`M^LP` of the LP schedule is an optimal solution to (R). -/
theorem theorem_2_5 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) :
    Shared.FeasibleR p r (mLP p r) ∧
      ∀ M : Fin n → ℝ, Shared.FeasibleR p r M → Shared.objR p w (mLP p r) ≤ Shared.objR p w M := by sorry

end SingleMachineSched.AlphaJSched
