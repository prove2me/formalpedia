-- Prove2me | Theorems.Thm_SAGA_Convex_lemma2_grad_variance
-- name    : SAGA.Convex.lemma2_grad_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:25:09.619988+00:00
-- url     : https://prove2.me/theorems/0d4481e3-d68f-4bad-96d7-29b8a3768f6b
-- title:
--   Lemma 2 — gradient differences bounded by Bregman divergences
-- statement:
--   Let $n\ge1$, $L>0$, and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be convex and differentiable with $L$-Lipschitz gradients $f_i'$; write $f=\frac1n\sum_i f_i$. Then for all points $\phi_1,\dots,\phi_n$ and $x^*$ in $\mathbb R^d$,
--
--   $$
--   \frac1n\sum_{i=1}^n\|f_i'(\phi_i)-f_i'(x^*)\|^2\le 2L\Big[\frac1n\sum_{i=1}^n f_i(\phi_i)-f(x^*)-\frac1n\sum_{i=1}^n\langle f_i'(x^*),\phi_i-x^*\rangle\Big].
--   $$
--
--   The bracket is the table part of the SAGA Lyapunov function; the lemma bounds the variance contributed by the stored gradients by it.
--
--   **Formalization Note** The page states no hypotheses for this lemma; its proof uses the standing assumptions (each $f_i$ convex with $L$-Lipschitz gradient), which are stated here.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 7, Lemma 2 (= Lemma 6, p. 11)

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- Lemma 2 (= Lemma 6), pp. 7 and 11: if each `fᵢ` is convex with `L`-Lipschitz gradient, then
for all points `φᵢ` and `x*`,
`(1/n) ∑ᵢ ‖f′ᵢ(φᵢ) - f′ᵢ(x*)‖² ≤ 2L [(1/n) ∑ᵢ fᵢ(φᵢ) - f(x*) - (1/n) ∑ᵢ ⟨f′ᵢ(x*), φᵢ - x*⟩]`. -/
theorem lemma2_grad_variance {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (φ : Fin n → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ i, ‖f' i (φ i) - f' i xs‖ ^ 2 ≤
      2 * L * ((1 / (n : ℝ)) * ∑ i, f i (φ i) - fAvg f xs
        - (1 / (n : ℝ)) * ∑ i, ⟪f' i xs, φ i - xs⟫) := by sorry

end SAGA.Convex
