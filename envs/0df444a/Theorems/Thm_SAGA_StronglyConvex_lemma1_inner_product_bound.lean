-- Prove2me | Theorems.Thm_SAGA_StronglyConvex_lemma1_inner_product_bound
-- name    : SAGA.StronglyConvex.lemma1_inner_product_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:54:20.347875+00:00
-- url     : https://prove2.me/theorems/fca1b3e8-db17-4c01-bb38-4d8976213d53
-- title:
--   Lemma 1 (= Lemma 5) — inner-product bound for averages of strongly convex smooth functions
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be differentiable with gradients $f_i'$. Suppose each $f_i$ is $\mu$-strongly convex ($\mu>0$) and each $f_i'$ is Lipschitz continuous with constant $L>0$. Write $f=\frac1n\sum_i f_i$ and $f'=\frac1n\sum_i f_i'$. Then for all $x,x^*\in\mathbb R^d$,
--
--   $$
--   \langle f'(x),x^*-x\rangle\;\le\;\frac{L-\mu}{L}\big[f(x^*)-f(x)\big]-\frac\mu2\|x^*-x\|^2-\frac{1}{2Ln}\sum_{i=1}^n\|f_i'(x^*)-f_i'(x)\|^2-\frac\mu L\langle f'(x^*),x-x^*\rangle .
--   $$
--
--   Here $x^*$ is an arbitrary point, not necessarily a minimizer. In the proof of Theorem 1 the lemma bounds the inner-product term $-2c\gamma\langle f'(x^k),x^k-x^*\rangle$ produced by expanding $c\|x^{k+1}-x^*\|^2$.
--
--   **Formalization Note** No relation between $\mu$ and $L$ is assumed: $\mu\le L$ follows from the hypotheses when $d\ge1$, and for $\mu=L$ the statement still holds (with equality for quadratics). The components are indexed by `Fin n`; $f$ and $f'$ are written out as averages.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, pp. 6-7, Lemma 1 (restated as Lemma 5, p. 10)

import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Lemma 1 (pp. 6–7, = Lemma 5, p. 10). `f = (1/n) Σ_i f_i`, each `f_i` `μ`-strongly convex with
`L`-Lipschitz gradient `f'_i`; `f' = (1/n) Σ_i f'_i`. The points `x` and `x*` (here `xs`) are
arbitrary. -/
theorem lemma1_inner_product_bound {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (x xs : EuclideanSpace ℝ (Fin d)) :
    ⟪(1 / (n : ℝ)) • ∑ i, f' i x, xs - x⟫_ℝ ≤
      (L - μ) / L * ((1 / (n : ℝ)) * ∑ i, f i xs - (1 / (n : ℝ)) * ∑ i, f i x)
        - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x - xs⟫_ℝ := by sorry

end SAGA.StronglyConvex
