-- Prove2me | Theorems.Thm_ProcFlex_DMGI_theorem_1
-- name    : ProcFlex.DMGI.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:26.345814+00:00
-- url     : https://prove2.me/theorems/24beceaa-8c57-4a6f-ab78-88cbd133d1bf
-- title:
--   Theorem 1: representation of robust measures in Γ
-- statement:
--   Let $f(A,d)=h(g(A,d),(\sum_{i\in S_t}d_i)_t)$, where $h$ is strictly increasing in profit at fixed category totals and $f$ is continuous in nonnegative demand. Suppose $U$ is nonempty, compact, nonnegative, and part-wise independently symmetric around $\mu$, with residual set $E$. Then the following minimum is attained:
--
--   $$
--   R^f(A,U)=\min_{K\in Q,\,\epsilon\in E} h\left(\delta^K_\mu(A)+\sum_t\sum_{r<t}\beta_{tr}\sum_{i=H_{tr}-k_{tr}+1}^{H_{tr}}\epsilon_{s_t,i},\;\left(\sum_{i\in S_t}(\mu_i+\epsilon_i)\right)_t\right).
--   $$
--
--   The representation shows that these robust scores depend on the design through its margin-group indices.
--
--   **Formalization Note** The category residuals use a fixed increasing product-index order, and the DMGI includes $z\ge0$. Compactness and nonemptiness of $U$ are added to make the printed minimum well posed.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 18, Theorem 1

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Theorem 1, p. 18: the attained DMGI representation of every robust
measure in the paper's class Γ. -/
theorem theorem_1 {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (h : ℝ → (Fin T → ℝ) → ℝ)
    (hh : ∀ y, StrictMono (fun x => h x y))
    (hcont : ContinuousOn (f S h A) {d | ∀ i, 0 ≤ d i})
    (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hU : IsSymmetricAround S U μ)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U) :
    IsLeast {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
      ∃ ε ∈ ((fun d => d - μ) '' U),
        v = h (dmgi S μ K A + blockSum S K ε)
          (catSum S (μ + ε))}
      (Rf S h A U) := by sorry

end ProcFlex.DMGI
