-- Prove2me | Theorems.Thm_PolicyGradTheory_LogBarrier_beck_gradient_rate
-- name    : PolicyGradTheory.LogBarrier.beck_gradient_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:54:57.975683+00:00
-- url     : https://prove2.me/theorems/e2410bc4-0db3-4211-8fa3-714b40f18d76
-- title:
--   Theorem E.1(3), p. 77 — gradient ascent with step 1/β on a β-smooth f ≤ M: min_{t<T} ‖∇f(x_t)‖ ≤ √(2β(M − f(x₀)))/√T
-- statement:
--   This is item 3 of Theorem E.1 (Theorem 10.15 of Beck, *First-Order Methods in Optimization*, 2017) in the unconstrained case, written for gradient ascent.
--
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with $\beta$-Lipschitz gradient, $\beta>0$, that is $\|\nabla f(x)-\nabla f(y)\|\le\beta\|x-y\|$ for all $x,y$, and suppose $f(x)\le M$ for all $x$. Let $x_{t+1}=x_t+\frac1\beta\nabla f(x_t)$ for $t\ge0$. Then for every $T\ge1$,
--   $$
--   \min_{t=0,1,\dots,T-1}\|\nabla f(x_t)\|\le\frac{\sqrt{2\beta\,(M-f(x_0))}}{\sqrt T}.
--   $$
--
--   The proof of Corollary 5.1 applies this to $f=L_\lambda$ with $\beta=\beta_\lambda$ to bound the number of iterations needed to reach an approximately stationary point.
--
--   **Formalization Note.** The page states the descent form for minimizing a function with optimal value $f(x^\star)$ over a set $C$, through the gradient mapping $G^\eta$; for $C=\mathbb R^d$ the page notes $G^\eta=\nabla f$. The statement here is that form applied to $-f$ (ascent), with an upper bound $M$ in place of the attained optimum $f(x^\star)$, which covers the attained case $M=\max f$. $\mathbb R^d$ is `EuclideanSpace ℝ ι` for a finite index type, and the minimum over $t<T$ is written as the existence of such a $t$. The page prints the radicand as $2\beta f(x_0)-f(x^\star)$; the parenthesized $2\beta(f(x_0)-f(x^\star))$ is Beck's statement and what the proof of Corollary 5.1 uses in (49).
-- source:
--   arXiv:1908.00261v5, Theorem E.1, item 3, p. 77 (Theorem 10.15 of Beck 2017), with Definition E.1 and the remark after (55)

import Mathlib

namespace PolicyGradTheory.LogBarrier

/-- Theorem E.1, item 3 (Theorem 10.15 of Beck [2017]), arXiv:1908.00261v5, p. 77, in the
unconstrained case `C = ℝ^d` (where the gradient mapping is `∇f`), posed for gradient *ascent*
on `f` (descent on `−f`): if `f : ℝ^d → ℝ` is differentiable with `β`-Lipschitz gradient, bounded
above by `M`, and `x_{t+1} = x_t + (1/β) ∇f(x_t)`, then
`min_{t=0,…,T−1} ‖∇f(x_t)‖ ≤ √(2β(M − f(x₀)))/√T`. -/
theorem beck_gradient_rate {ι : Type*} [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ) (β : ℝ)
    (hβ : 0 < β) (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (M : ℝ) (hM : ∀ x, f x ≤ M) (x : ℕ → EuclideanSpace ℝ ι)
    (hx : ∀ t, x (t + 1) = x t + (1 / β) • gradient f (x t)) :
    ∀ T : ℕ, 0 < T → ∃ t < T,
      ‖gradient f (x t)‖ ≤ Real.sqrt (2 * β * (M - f (x 0))) / Real.sqrt T := by sorry

end PolicyGradTheory.LogBarrier
