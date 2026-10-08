-- Prove2me | Theorems.Thm_ProductFraming_Nest_proposition_3
-- name    : ProductFraming.Nest.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:12.505374+00:00
-- url     : https://prove2.me/theorems/ce274dc9-54f2-4c93-a4e8-3568c8f53965
-- title:
--   Proposition 3 — $1/\gamma = \max_\Lambda \mathbb E[X/\mathbb E[\min(X,Y)\mid X]]$
-- statement:
--   Fix $m\ge1$. Let $\gamma$ be the optimal value of program (5), and let $Y$ be independent of $X$ with the same law. Then the minimum $\gamma$ of (5) is attained, and $1/\gamma$ is the optimal value of program (6):
--   $$\frac1\gamma=\max_{\Lambda}\ \mathbb E\Big[\frac{X}{\mathbb E[\min(X,Y)\mid X]}\Big]=\max_\Lambda\ \sum_{x\in[m]}\lambda(x)\,\frac{x}{\sum_{y=1}^{x}\Lambda(y)}$$
--   subject to $1=\Lambda(1)\ge\Lambda(2)\ge\dots\ge\Lambda(m)\ge0$ and $\Lambda(x+1)\sum_{y=1}^{m}\Lambda(y)\ge\sum_{y=x+1}^{m}\Lambda(y)$ for $x=1,\dots,m-1$, where $\lambda(x)=\Lambda(x)-\Lambda(x+1)$ and $\Lambda(m+1)=0$.
--
--   This reduces the min–max program (5) to a maximization over NBUE distributions only, which is then bounded by the exponential case.
--
--   **Formalization Note** The statement asserts the existence of $\gamma$ that is the least value of the objective of (5) over its feasible set, and that $1/\gamma$ is the greatest value of the objective of (6) over its feasible set (both attained).
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, p. 10, Proposition 3 (proof p. 36)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Program

namespace ProductFraming.Nest

open Finset

/-- Proposition 3 (Gallego, Li, Truong, Wang 2020, p. 10): the minimum `γ` of (5) is attained, and
`1/γ` is the maximum of `E[X / E[min(X, Y) | X]]` over the tails `Λ` feasible for (6). -/
theorem proposition_3 (m : ℕ) (hm : 1 ≤ m) :
    ∃ γ : ℝ, IsLeast {J : ℝ | ∃ U Λ : ℕ → ℝ, Feasible5 m U Λ ∧ J = J5 hm U Λ} γ ∧
      IsGreatest {t : ℝ | ∃ Λ : ℕ → ℝ, Feasible6 m Λ ∧ t = ratio6 m Λ} (1 / γ) := by sorry

end ProductFraming.Nest
