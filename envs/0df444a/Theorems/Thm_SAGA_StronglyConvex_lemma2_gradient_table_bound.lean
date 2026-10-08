-- Prove2me | Theorems.Thm_SAGA_StronglyConvex_lemma2_gradient_table_bound
-- name    : SAGA.StronglyConvex.lemma2_gradient_table_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:54:22.62398+00:00
-- url     : https://prove2.me/theorems/a0f5ba76-694d-454c-9882-b86ad61cc797
-- title:
--   Lemma 2 (= Lemma 6) — gradient differences bounded by the Lyapunov table term
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be convex and differentiable, with gradients $f_i'$ Lipschitz continuous with constant $L>0$. Write $f=\frac1n\sum_i f_i$. Then for all points $\phi_1,\dots,\phi_n$ and $x^*$ in $\mathbb R^d$,
--
--   $$
--   \frac1n\sum_{i=1}^n\|f_i'(\phi_i)-f_i'(x^*)\|^2\;\le\;2L\Big[\frac1n\sum_{i=1}^n f_i(\phi_i)-f(x^*)-\frac1n\sum_{i=1}^n\langle f_i'(x^*),\phi_i-x^*\rangle\Big].
--   $$
--
--   The bracket on the right is the table part of the Lyapunov function $T$ of Theorem 1. The lemma controls the variance contributed by the stale gradients in the table.
--
--   **Formalization Note** The paper states the lemma without hypotheses ("for all $\phi_i$ and $x^*$"); its proof applies the standard inequality for convex functions with $L$-Lipschitz gradient, so those standing assumptions of the paper (p. 1) are the hypotheses here. Strong convexity is not needed. $x^*$ is arbitrary.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 7, Lemma 2 (restated as Lemma 6, p. 11)

import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Lemma 2 (p. 7, = Lemma 6, p. 11), under the standing assumptions of p. 1: each `f_i` convex
with `L`-Lipschitz gradient `f'_i` (the proof's "standard inequality" needs exactly these).
`f = (1/n) Σ_i f_i`; the points `φ_i` and `x*` (here `xs`) are arbitrary. -/
theorem lemma2_gradient_table_bound {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (φ : Fin n → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ i, ‖f' i (φ i) - f' i xs‖ ^ 2 ≤
      2 * L * ((1 / (n : ℝ)) * ∑ i, f i (φ i) - (1 / (n : ℝ)) * ∑ i, f i xs
        - (1 / (n : ℝ)) * ∑ i, ⟪f' i xs, φ i - xs⟫_ℝ) := by sorry

end SAGA.StronglyConvex
