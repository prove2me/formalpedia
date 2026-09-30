-- Prove2me | Theorems.Thm_SingleMachineSched_LPRelax_lemma_2_1
-- name    : SingleMachineSched.LPRelax.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T04:02:09.604197+00:00
-- url     : https://prove2.me/theorems/5b0843f3-7f91-4013-af01-04d42c427dec
-- title:
--   Lemma 2.1 — (D) has an optimal $0/1$ solution
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j \ge 0$, and let the horizon $T \in \mathbb N$ bound the makespan of some feasible nonpreemptive schedule. Then the preemptive time-indexed relaxation (D) has an optimal solution with integral entries: there is a feasible $y^*$ with
--
--   $$y^*_{j\tau} \in \{0, 1\} \quad \text{for all } j \text{ and } \tau$$
--
--   such that $\sum_j w_j C_j(y^*) \le \sum_j w_j C_j(y)$ for every feasible $y$, where $C_j(\cdot)$ is given by (2.1).
--
--   The lemma reflects that, after eliminating $C_j$ with (2.1), (D) is a transportation problem. It is the starting point of the interchange argument for Theorem 2.2.
--
--   **Formalization Note** Optimality is stated directly (the solution attains the minimum over all feasible $y$), not through the value $Z_D$. The paper's standing assumption is $w_j > 0$; the statement is made for $w_j \ge 0$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 170, Lemma 2.1

import Mathlib
import Definitions.Def_SingleMachineSched_LPRelax_RelaxationD

namespace SingleMachineSched.LPRelax

/-- Lemma 2.1: (D) has an optimal solution with `y_{jτ} ∈ {0, 1}` for all `j` and `τ`. -/
theorem lemma_2_1 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) (T : ℕ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hT : IsMakespanBound p r T) :
    ∃ y : Fin n → ℕ → ℝ, FeasibleD p r T y ∧ (∀ j τ, y j τ = 0 ∨ y j τ = 1) ∧
      ∀ y' : Fin n → ℕ → ℝ, FeasibleD p r T y' → objD p r w T y ≤ objD p r w T y' := by sorry

end SingleMachineSched.LPRelax
