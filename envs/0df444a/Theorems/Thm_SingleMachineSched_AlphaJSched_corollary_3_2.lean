-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_corollary_3_2
-- name    : SingleMachineSched.AlphaJSched.corollary_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:19:06.923019+00:00
-- url     : https://prove2.me/theorems/4355355c-3cad-4e20-b193-14a49f728570
-- title:
--   Corollary 3.2 — completion times in an $(\alpha_j)$-schedule
-- statement:
--   Let $n$ jobs have integral processing times $p_j>0$, integral release dates $r_j\ge0$ and weights $w_j>0$, indexed in nonincreasing order of $w_j/p_j$, and let $\boldsymbol\alpha=(\alpha_k)$ with $0<\alpha_k\le1$ for every $k$. Then for every job $j$ the completion time of $j$ in the $(\alpha_j)$-schedule satisfies
--   $$C^{\boldsymbol\alpha}_j\ \le\ t_j(\alpha_j)+\sum_{k:\ \alpha_k\le\eta_k(\alpha_j)}\bigl(1+\alpha_k-\eta_k(\alpha_j)\bigr)p_k ,$$
--   where $t_j(\alpha_j)$ is the $\alpha_j$-point of $j$ and $\eta_k(\alpha_j)$ the fraction of job $k$ processed by time $t_j(\alpha_j)$, both in the LP schedule.
--
--   The sum runs over the jobs that precede $j$ in the $(\alpha_j)$-schedule; it includes $k=j$, for which $\eta_j(\alpha_j)=\alpha_j$ and the term is $p_j$. This bound is the deterministic core of all the randomized analyses of the paper.
--
--   **Formalization Note.** The $(\alpha_j)$-schedule is the closed form of list scheduling in lexicographic (α-point, index) order. The paper obtains the corollary from Lemma 3.1 on an auxiliary schedule, the $(\alpha_j)$-Conversion; the corollary is stated directly for the $(\alpha_j)$-schedule, as in the paper.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 179, Corollary 3.2

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaJSchedule

namespace SingleMachineSched.AlphaJSched

/-- Corollary 3.2: for `α ∈ (0, 1]ⁿ`, the completion time of job `j` in the `(α_j)`-schedule is
at most `t_j(α_j) + Σ_{k : α_k ≤ η_k(α_j)} (1 + α_k − η_k(α_j)) p_k`. -/
theorem corollary_3_2 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j)
    (α : Fin n → ℝ) (hα : ∀ k, 0 < α k ∧ α k ≤ 1) (j : Fin n) :
    (alphaCompletion p r α j : ℝ) ≤
      alphaPoint p (lpSet p r) j (α j) +
        ∑ k ∈ Finset.univ.filter (fun k => α k ≤ eta p (lpSet p r) j (α j) k),
          (1 + α k - eta p (lpSet p r) j (α j) k) * (p k : ℝ) := by sorry

end SingleMachineSched.AlphaJSched
