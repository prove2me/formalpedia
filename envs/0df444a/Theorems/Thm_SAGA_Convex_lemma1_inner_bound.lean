-- Prove2me | Theorems.Thm_SAGA_Convex_lemma1_inner_bound
-- name    : SAGA.Convex.lemma1_inner_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:25:05.878414+00:00
-- url     : https://prove2.me/theorems/b6f50a16-3afd-4765-9a8f-b33b780bcdbd
-- title:
--   Lemma 1 — inner-product bound for averages of strongly convex smooth functions
-- statement:
--   Let $n\ge1$, $L>0$ and $\mu\ge0$. Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be differentiable with gradients $f_i'$, each $f_i$ $\mu$-strongly convex (convex when $\mu=0$) with $L$-Lipschitz gradient, and let $f=\frac1n\sum_i f_i$, $f'=\frac1n\sum_i f_i'$. Then for all $x,x^*\in\mathbb R^d$,
--
--   $$
--   \langle f'(x),x^*-x\rangle\le\frac{L-\mu}{L}\big[f(x^*)-f(x)\big]-\frac\mu2\|x^*-x\|^2-\frac1{2Ln}\sum_{i=1}^n\|f_i'(x^*)-f_i'(x)\|^2-\frac\mu L\langle f'(x^*),x-x^*\rangle .
--   $$
--
--   The proof of Theorem 2 uses it with $\mu=0$, where it reads $\langle f'(x),x^*-x\rangle\le f(x^*)-f(x)-\frac1{2Ln}\sum_i\|f_i'(x^*)-f_i'(x)\|^2$; it controls the cross term produced by the $c\|x-x^*\|^2$ part of the Lyapunov function.
--
--   **Formalization Note** $\mu$-strong convexity is Mathlib's `StrongConvexOn Set.univ μ`, whose modulus is $\frac\mu2\|x-y\|^2$, the paper's convention. The gradients are given maps with `HasGradientAt (f i) (f' i x) x`.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, pp. 6-7, Lemma 1 (= Lemma 5, p. 10)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- Lemma 1 (= Lemma 5), pp. 6–7 and 10: for `f = (1/n) ∑ fᵢ` with each `fᵢ` `μ`-strongly convex
(`μ ≥ 0`; `μ = 0` is plain convexity, the case used for Theorem 2) and with `L`-Lipschitz
gradients, for all `x` and `x*`,
`⟨f′(x), x* - x⟩ ≤ ((L - μ)/L)[f(x*) - f(x)] - (μ/2)‖x* - x‖²
  - (1/(2Ln)) ∑ᵢ ‖f′ᵢ(x*) - f′ᵢ(x)‖² - (μ/L)⟨f′(x*), x - x*⟩`. -/
theorem lemma1_inner_bound {d n : ℕ} (hn : 0 < n) {L μ : ℝ} (hL : 0 < L) (hμ : 0 ≤ μ)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, StrongConvexOn Set.univ μ (f i))
    (x xs : EuclideanSpace ℝ (Fin d)) :
    ⟪gradAvg f' x, xs - x⟫ ≤
      (L - μ) / L * (fAvg f xs - fAvg f x) - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪gradAvg f' xs, x - xs⟫ := by sorry

end SAGA.Convex
