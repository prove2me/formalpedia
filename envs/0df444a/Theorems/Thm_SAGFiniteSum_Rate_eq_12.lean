-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_eq_12
-- name    : SAGFiniteSum.Rate.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:35.523165+00:00
-- url     : https://prove2.me/theorems/12270397-e5a2-4a44-b39f-70f3dac8062e
-- title:
--   Eq. (12), p. 37 — strong convexity of g: 2g(x + deᵀy) ≥ 2g(x) + 2d g′(x)ᵀeᵀy + μd²‖eᵀy‖²
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be differentiable with gradients $f'_i$, let $g=\frac1n\sum_if_i$ and $g'=\frac1n\sum_if'_i$, and let $\mu\ge0$ be such that $x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex. Then for every $x\in\mathbb R^p$, every table $y=(y_1,\dots,y_n)$ and every scalar $d$, with $e^\top y=\sum_iy_i$,
--   $$
--   2g(x+de^\top y)\ \ge\ 2g(x)+2d\,g'(x)^\top e^\top y+\mu d^2\|e^\top y\|^2 .
--   $$
--
--   This is the strong-convexity lower bound that App. B.3 applies at the state $(y^{k-1},x^{k-1})$ to the term $-(1-\delta)2h\,g(x^{k-1}+de^\top y^{k-1})$ of the Lyapunov function.
--
--   **Formalization Note** The page states the inequality at $(x^{k-1},y^{k-1})$; the statement here is for every $x$ and $y$, which is the same claim. App. B uses "the convention that $\mu\ge0$", so $\mu=0$ (plain convexity) is included. Only differentiability of the $f_i$ is assumed besides strong convexity.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.3, Eq. (12), p. 37

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- Inequality (12) (arXiv:1309.2388v2, App. B.3, p. 37). If `g = (1/n) ∑ᵢ fᵢ` is `μ`-strongly
convex (`g − (μ/2)‖·‖²` convex, `μ ≥ 0`) and differentiable with gradient `g' = (1/n) ∑ᵢ f'ᵢ`,
then for every `x`, every table `y` and every scalar `d`,
`2g(x + d eᵀy) ≥ 2g(x) + 2d g'(x)ᵀeᵀy + μd²‖eᵀy‖²`, where `eᵀy = ∑ᵢ yᵢ`. -/
theorem eq_12 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x) (μ : ℝ) (hμ : 0 ≤ μ)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (d : ℝ) (x : EuclideanSpace ℝ (Fin p)) (y : Fin n → EuclideanSpace ℝ (Fin p)) :
    2 * SAGA.Convex.fAvg f x + 2 * d * ⟪SAGA.Convex.gradAvg f' x, ∑ i, y i⟫
        + μ * d ^ 2 * ‖∑ i, y i‖ ^ 2
      ≤ 2 * SAGA.Convex.fAvg f (x + d • ∑ i, y i) := by sorry

end SAGFiniteSum.Rate
