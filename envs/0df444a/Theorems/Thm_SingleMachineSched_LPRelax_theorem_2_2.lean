-- Prove2me | Theorems.Thm_SingleMachineSched_LPRelax_theorem_2_2
-- name    : SingleMachineSched.LPRelax.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T04:06:36.998489+00:00
-- url     : https://prove2.me/theorems/4e3fe5d9-96a2-4186-8e04-2c52b864b227
-- title:
--   Theorem 2.2 — the LP schedule's slot vector $y^{LP}$ is optimal for (D)
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j \ge 0$, indexed so that
--
--   $$\frac{w_1}{p_1} \ge \frac{w_2}{p_2} \ge \cdots \ge \frac{w_n}{p_n},$$
--
--   and let the horizon $T \in \mathbb N$ bound the makespan of some feasible nonpreemptive schedule. Let $y^{LP}_{j\tau} = 1$ if the LP schedule processes $j$ in $[\tau, \tau+1)$ and $0$ otherwise. Then
--
--   1. $y^{LP}$ is feasible for (D) with horizon $T$;
--   2. for every feasible $y$, $\sum_j w_j C_j(y^{LP}) \le \sum_j w_j C_j(y)$, where $C_j(\cdot)$ is given by (2.1).
--
--   So an optimal solution of (D), which has a pseudopolynomial number of variables, is read off the LP schedule.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based, and the sortedness is the hypothesis `j ≤ k → w_k/p_k ≤ w_j/p_j`. Feasibility includes that $y^{LP}$ vanishes from slot $T$ on, i.e. that the LP schedule finishes by $T$. The statement is made for $w_j \ge 0$ (the paper's standing assumption is $w_j > 0$).
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 171, Theorem 2.2 ($y^{LP}$ defined on p. 170)

import Mathlib
import Definitions.Def_SingleMachineSched_LPRelax_LPSchedule
import Definitions.Def_SingleMachineSched_LPRelax_RelaxationD

namespace SingleMachineSched.LPRelax

/-- Theorem 2.2: with the jobs indexed by nonincreasing `w_j / p_j`, the slot vector `y^LP` of
the LP schedule is an optimal solution to (D). -/
theorem theorem_2_2 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) (T : ℕ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (hT : IsMakespanBound p r T) :
    FeasibleD p r T (yLP p r) ∧
      ∀ y : Fin n → ℕ → ℝ, FeasibleD p r T y → objD p r w T (yLP p r) ≤ objD p r w T y := by sorry

end SingleMachineSched.LPRelax
