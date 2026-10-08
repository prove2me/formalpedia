-- Prove2me | Theorems.Thm_SAG_SmallStep_cocoercivity_sum
-- name    : SAG.SmallStep.cocoercivity_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:20.430465+00:00
-- url     : https://prove2.me/theorems/38a2fe49-9681-435f-a81b-9fa44ac2cf3c
-- title:
--   §A.5 Step 1, p. 20 — summed co-coercivity: $\sum_i\|f'_i(x)-f'_i(y)\|^2\le nL\langle g'(x)-g'(y),x-y\rangle$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be convex and differentiable, with gradients $f'_i$ that are Lipschitz continuous with constant $L>0$: $\|f'_i(x)-f'_i(y)\|\le L\|x-y\|$. Let $g=\frac1n\sum_i f_i$, so $g'=\frac1n\sum_i f'_i$. Then for all $x,y\in\mathbb R^p$,
--   $$
--   \sum_{i=1}^n\|f'_i(x)-f'_i(y)\|^2\;\le\;nL\,\big(g'(x)-g'(y)\big)^\top(x-y).
--   $$
--
--   The paper uses this at $y=x^*$ to bound the term $(f'(x^{k-1})-f'(x^*))^\top(f'(x^{k-1})-f'(x^*))$ produced by Lemma 1 in the proof of Proposition 1. It is the co-coercivity of each convex $L$-smooth $f_i$ ([Nesterov, 2004, Theorem 2.1.5]) summed over $i$.
--
--   **Formalization Note** The display is stated for an arbitrary pair $(x,y)$; the page has $(x^{k-1},x^*)$. The gradients are an explicit map `f'` linked to the $f_i$ by `HasGradientAt`; $g'$ is `SAGA.Convex.gradAvg f'`.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 20, §A.5 Step 1, display after "The third line is obtained using the Lipschitz property of the gradient"; convexity of each f_i from p. 13, §A.1

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

open scoped RealInnerProductSpace

namespace SAG.SmallStep

/-- §A.5 Step 1 (arXiv:1202.6258v4, p. 20): the co-coercivity of each convex `fᵢ` with
`L`-Lipschitz gradient, summed over `i`:
`∑ᵢ ‖f'ᵢ(x) − f'ᵢ(y)‖² ≤ n L ⟪g'(x) − g'(y), x − y⟫`. -/
theorem cocoercivity_sum {p n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin p)) :
    ∑ i, ‖f' i x - f' i y‖ ^ 2
      ≤ (n : ℝ) * L * ⟪SAGA.Convex.gradAvg f' x - SAGA.Convex.gradAvg f' y, x - y⟫ := by sorry

end SAG.SmallStep
