-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_lemma_A_1
-- name    : SGDKaczmarz.SGD.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:45.54808+00:00
-- url     : https://prove2.me/theorems/766efb95-6822-4d56-9feb-7454d998b4e7
-- title:
--   Lemma A.1 (co-coercivity), p. 21 — ‖∇f(x) − ∇f(y)‖² ≤ L⟨x − y, ∇f(x) − ∇f(y)⟩
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $f : \mathcal H \to \mathbb R$ a differentiable convex function whose gradient is Lipschitz with constant $L \ge 0$. Then for all $x, y \in \mathcal H$
--   $$\|\nabla f(x) - \nabla f(y)\|_2^2 \le L\,\langle x - y, \nabla f(x) - \nabla f(y)\rangle.$$
--
--   This is the co-coercivity of the gradient. In the proof of Theorem 2.1 it bounds the squared gradient difference of each component $f_i$ by an inner product that can then be averaged over $i$.
--
--   **Formalization Note** The page states the lemma "for a smooth function $f$ whose gradient has Lipschitz constant $L$" and calls the auxiliary functions of its proof convex; convexity of $f$ is stated as a hypothesis here, because without it the inequality fails ($f(x) = -x^2$ on $\mathbb R$, $L = 2$). Every use in the paper is for a convex $f_i$.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, Lemma A.1, p. 21

import Mathlib

open scoped NNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Lemma A.1 (Co-coercivity), p. 21: for a differentiable convex `f` whose gradient has Lipschitz
constant `L`, `‖∇f(x) − ∇f(y)‖² ≤ L ⟨x − y, ∇f(x) − ∇f(y)⟩`. -/
theorem lemma_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hf : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f) (L : ℝ≥0)
    (hL : LipschitzWith L (gradient f)) (x y : H) :
    ‖gradient f x - gradient f y‖ ^ 2 ≤ (L : ℝ) * ⟪x - y, gradient f x - gradient f y⟫_ℝ := by sorry

end SGDKaczmarz.SGD
