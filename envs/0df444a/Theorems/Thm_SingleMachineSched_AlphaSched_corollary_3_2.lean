-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_corollary_3_2
-- name    : SingleMachineSched.AlphaSched.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:12:30.428991+00:00
-- url     : https://prove2.me/theorems/fbafc96b-db11-4a85-9499-a1ae60d2cb43
-- title:
--   Corollary 3.2 — completion times of the $(\alpha_j)$-schedule via $\alpha$-points
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j > 0$, indexed by nonincreasing $w_j/p_j$. Let $\boldsymbol\alpha = (\alpha_k)$ with $0 < \alpha_k \le 1$ for all $k$, and let $C^{\boldsymbol\alpha}_j$ be the completion time of job $j$ in the $(\alpha_j)$-schedule. With $t_j(\alpha_j)$ the $\alpha_j$-point of $j$ and $\eta_k(\alpha_j)$ the fraction of job $k$ processed by time $t_j(\alpha_j)$, both in the LP schedule,
--
--   $$C^{\boldsymbol\alpha}_j \le t_j(\alpha_j) + \sum_{k \,:\, \alpha_k \le \eta_k(\alpha_j)} \big(1 + \alpha_k - \eta_k(\alpha_j)\big)\, p_k .$$
--
--   The sum ranges over all jobs $k$, including $k = j$, for which $\eta_j(\alpha_j) = \alpha_j$ and the term is $p_j$. This is the basic bound from which the paper's analyses of the $\alpha$-schedule and the $(\alpha_j)$-schedule start.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 179, Corollary 3.2

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaSchedule

namespace SingleMachineSched.AlphaSched

open Classical in
/-- Corollary 3.2 (Goemans et al. 2002, p. 179): for every `α ∈ (0, 1]ⁿ`, the completion time of
job `j` in the `(α_j)`-schedule satisfies
`C^α_j ≤ t_j(α_j) + Σ_{k : α_k ≤ η_k(α_j)} (1 + α_k - η_k(α_j)) p_k`,
where `α`-points and `η` are taken in the LP schedule. The sum includes `k = j`. -/
theorem corollary_3_2 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k ∧ α k ≤ 1) (j : Fin n) :
    alphaCompletion p r α j ≤
      alphaPoint p (lpSet p r) j (α j) +
        ∑ k ∈ Finset.univ.filter (fun k => α k ≤ eta p (lpSet p r) j (α j) k),
          (1 + α k - eta p (lpSet p r) j (α j) k) * (p k : ℝ) := by sorry

end SingleMachineSched.AlphaSched
