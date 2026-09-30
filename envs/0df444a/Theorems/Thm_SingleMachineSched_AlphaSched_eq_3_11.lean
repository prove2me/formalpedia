-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_eq_3_11
-- name    : SingleMachineSched.AlphaSched.eq_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:13:45.223302+00:00
-- url     : https://prove2.me/theorems/f972cfa4-d659-4b47-99d5-8c53a404aaa5
-- title:
--   Eq. (3.11) — the structured bound on $C^{\alpha}_j$ through $N_1$, $N_2$ and $\mu_k$
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j > 0$, indexed by nonincreasing $w_j/p_j$. Let $0 < \alpha_k \le 1$ for all $k$, and fix a job $j$. In the LP schedule, let $t_j(0^+)$ be the start time of $j$, $\eta_k = \eta_k(\alpha_j)$ the fraction of job $k$ processed by the $\alpha_j$-point of $j$, $N_2$ the set of jobs $k \ne j$ processed between the start and the completion of $j$, $N_1$ the set of the other jobs $k \ne j$, and $\mu_k$ the fraction of $j$ processed before the start of $k$. Then the completion time of $j$ in the $(\alpha_j)$-schedule satisfies
--
--   $$C^{\boldsymbol\alpha}_j \le t_j(0^+) + \sum_{\substack{k \in N_1 \\ \alpha_k \le \eta_k}} (1 + \alpha_k - \eta_k)\, p_k + \sum_{\substack{k \in N_2 \\ \alpha_j > \mu_k}} (1 + \alpha_k)\, p_k + (1 + \alpha_j)\, p_j .$$
--
--   The bound separates the delay of job $j$ caused by jobs of $N_1$ from that caused by jobs of $N_2$; the two properties of the density in Lemma 3.6 control the two sums.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 183, Eq. (3.11)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaSchedule

namespace SingleMachineSched.AlphaSched

open Classical in
/-- Eq. (3.11) (Goemans et al. 2002, p. 183): for every `α ∈ (0, 1]ⁿ`, with `η_k = η_k(α_j)`
taken in the LP schedule,
`C^α_j ≤ t_j(0⁺) + Σ_{k ∈ N₁, α_k ≤ η_k} (1 + α_k - η_k) p_k
  + Σ_{k ∈ N₂, α_j > μ_k} (1 + α_k) p_k + (1 + α_j) p_j`. -/
theorem eq_3_11 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k ∧ α k ≤ 1) (j : Fin n) :
    alphaCompletion p r α j ≤
      startTime (lpSet p r) j +
        ∑ k ∈ (N1 p r j).filter (fun k => α k ≤ eta p (lpSet p r) j (α j) k),
          (1 + α k - eta p (lpSet p r) j (α j) k) * (p k : ℝ) +
        ∑ k ∈ (N2 p r j).filter (fun k => mu p r j k < α j), (1 + α k) * (p k : ℝ) +
        (1 + α j) * (p j : ℝ) := by sorry

end SingleMachineSched.AlphaSched
