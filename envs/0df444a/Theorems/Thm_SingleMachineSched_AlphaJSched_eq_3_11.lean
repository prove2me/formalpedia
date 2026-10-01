-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_eq_3_11
-- name    : SingleMachineSched.AlphaJSched.eq_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:20:15.801799+00:00
-- url     : https://prove2.me/theorems/495e1fd4-7a5b-44e8-9ba5-26f23ebf85d8
-- title:
--   Eq. (3.11) — Corollary 3.2 rewritten over $N_1$ and $N_2$
-- statement:
--   Let $n$ jobs have integral processing times $p_j>0$, integral release dates $r_j\ge0$ and weights $w_j>0$, indexed in nonincreasing order of $w_j/p_j$, and let $0<\alpha_k\le1$ for every $k$. Fix a job $j$; let $t_j(0^+)$, $N_1$, $N_2$ and $\mu_k$ be as in the LP schedule, and write $\eta_k=\eta_k(\alpha_j)$. Then the completion time of $j$ in the $(\alpha_j)$-schedule satisfies
--   $$C^{\boldsymbol\alpha}_j\ \le\ t_j(0^+)+\sum_{\substack{k\in N_1\\ \alpha_k\le\eta_k}}(1+\alpha_k-\eta_k)\,p_k+\sum_{\substack{k\in N_2\\ \alpha_j>\mu_k}}(1+\alpha_k)\,p_k+(1+\alpha_j)\,p_j .$$
--
--   The first sum is the delay caused by jobs outside $j$'s processing window, the second the delay caused by jobs inside it. Property (i) of Lemma 3.11 bounds the first and property (ii) the second in the proof of Theorem 3.9.
--
--   **Formalization Note.** $\eta_k$ is taken at $\alpha_j$ for every $k$, as in the paper, where it is constant in $\alpha_j$ on $N_1$.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 183, Section 3.2, Eq. (3.11)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints
import Definitions.Def_SingleMachineSched_AlphaJSched_LPStructure
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule

namespace SingleMachineSched.AlphaJSched

/-- Equation (3.11): for `α ∈ (0, 1]ⁿ`, with `η_k := η_k(α_j)`,
`C^α_j ≤ t_j(0⁺) + Σ_{k ∈ N₁, α_k ≤ η_k} (1 + α_k − η_k) p_k + Σ_{k ∈ N₂, α_j > μ_k} (1 + α_k) p_k
+ (1 + α_j) p_j`. -/
theorem eq_3_11 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k ∧ α k ≤ 1) (j : Fin n) :
    (alphaCompletion p r α j : ℝ) ≤
      startTime (lpSet p r) j +
        ∑ k ∈ (N1 p r j).filter (fun k => α k ≤ eta p (lpSet p r) j (α j) k),
          (1 + α k - eta p (lpSet p r) j (α j) k) * (p k : ℝ) +
        ∑ k ∈ (N2 p r j).filter (fun k => mu p r j k < α j), (1 + α k) * (p k : ℝ) +
        (1 + α j) * (p j : ℝ) := by sorry

end SingleMachineSched.AlphaJSched
