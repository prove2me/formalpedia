-- Prove2me | Theorems.Thm_ProxBundle_GPB_corollary_B_2
-- name    : ProxBundle.GPB.corollary_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:26.044994+00:00
-- url     : https://prove2.me/theorems/17a647db-da20-4b68-ab70-b6a1fecd78e4
-- title:
--   Corollary B.2, p. 27 — recursion bounds
-- statement:
--   Let $\theta\ge1$, $\delta>0$, and let $(\eta_j)$ and $(\alpha_j)$ be nonnegative real sequences satisfying $\eta_j\le\alpha_{j-1}-\theta\alpha_j+\delta$ for every $j\ge1$. Define $B=\alpha_0/\delta$ when $\theta=1$, and otherwise
--   $$
--   B=\min\left\{\frac{\alpha_0}{\delta},\frac{\theta}{\theta-1}\log\left(\frac{\alpha_0(\theta-1)}{\delta}+1\right)\right\}.
--   $$
--   For every integer $k\ge1$ with $k\ge B$, some $1\le j\le k$ satisfies $\eta_j\le2\delta$. Also, $\alpha_k\le\alpha_0+k\delta$ for every $k\ge1$.
--
--   These estimates convert a one-step scalar recursion into a finite hitting-time bound and an upper bound on the state sequence.
--
--   **Formalization Note** The $\theta=1$ convention is an explicit conditional, avoiding division by zero.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 27, Corollary B.2

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace ProxBundle.GPB

/-- Corollary B.2, p. 27, including its θ = 1 convention. -/
theorem corollary_B_2 (θ δ : ℝ) (η α : ℕ → ℝ)
    (hθ : 1 ≤ θ) (hδ : 0 < δ)
    (hη : ∀ j, 0 ≤ η j) (hα : ∀ j, 0 ≤ α j)
    (hrec : ∀ j, 1 ≤ j → η j ≤ α (j - 1) - θ * α j + δ) :
    (∀ k : ℕ, 1 ≤ k →
      (if θ = 1 then α 0 / δ
       else min (α 0 / δ)
         (θ / (θ - 1) * Real.log (α 0 * (θ - 1) / δ + 1))) ≤ (k : ℝ) →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ η j ≤ 2 * δ) ∧
    (∀ k : ℕ, 1 ≤ k → α k ≤ α 0 + (k : ℝ) * δ) := by sorry

end ProxBundle.GPB
