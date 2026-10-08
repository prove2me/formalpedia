-- Prove2me | Theorems.Thm_PolicyGradTheory_ProjGA_beck_projected_gradient_rate
-- name    : PolicyGradTheory.ProjGA.beck_projected_gradient_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:19:15.913008+00:00
-- url     : https://prove2.me/theorems/e46d63d1-fc5e-4c00-a5bb-22d1be05baed
-- title:
--   Theorem E.1(3), p. 77 (Beck 2017, Thm 10.15) — projected gradient with η = 1/β: min_{t<T} ‖G^η(x_t)‖ ≤ √(2β(f(x₀) − f(x*)))/√T
-- statement:
--   Consider problem (54), $\min_{x\in C}f(x)$, where $C\subseteq\mathbb R^d$ is nonempty, closed and convex, and $f$ is differentiable at every point of $C$ and $\beta$-smooth there, with $\beta>0$:
--   $$
--   \|\nabla f(x)-\nabla f(y)\|\le\beta\|x-y\|\qquad\text{for all }x,y\in C.
--   $$
--   Let $x^*\in C$ be a minimizer of $f$ over $C$, and let $P_C$ be the Euclidean projection onto $C$. With step size $\eta=1/\beta$, define the gradient mapping (55)
--   $$
--   G^\eta(x)=\frac1\eta\big(x-P_C(x-\eta\nabla f(x))\big),
--   $$
--   and let $x_0\in C$ and $x_{t+1}=P_C(x_t-\eta\nabla f(x_t))$ for $t\ge0$ (projected gradient descent).
--
--   **Theorem (Beck 2017, Theorem 10.15, item 3).** For every $T\ge1$,
--   $$
--   \min_{t=0,1,\dots,T-1}\|G^\eta(x_t)\|\le\frac{\sqrt{2\beta\,(f(x_0)-f(x^*))}}{\sqrt T}.
--   $$
--
--   This is the standard sublinear rate at which projected gradient descent reaches approximate first-order stationarity on a smooth, possibly non-convex problem. The proof of Theorem 4.1 applies it to $f=-V^\pi(\mu)$ on the policy simplex.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ ι` for a finite index type $\iota$. Assumption E.1 asks for $\beta$-smoothness over the interior of the domain of $f$; here smoothness is assumed on $C$ only, which is what Lemma D.3 provides for the policy simplex and is enough because all iterates and the segments between them lie in $C$. The radicand is $2\beta(f(x_0)-f(x^*))$ as in Beck and as used on p. 49; the printed item 3 misplaces the parenthesis. Items 1 and 2 of the theorem are not stated.
-- source:
--   arXiv:1908.00261v5, Theorem E.1 item 3, p. 77 (citing Beck 2017, Theorem 10.15); problem (54), p. 76; Assumption E.1, Definition E.1 (55), p. 77

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_Projection

namespace PolicyGradTheory.ProjGA

/-- Theorem E.1, item 3 (Theorem 10.15 of Beck 2017), arXiv:1908.00261v5, p. 77, for problem (54)
`min_{x∈C} f(x)` over a nonempty closed convex `C ⊆ ℝ^ι`, with `f` differentiable on `C` and
`β`-smooth there: projected gradient descent `x_{t+1} = P_C(x_t − (1/β)∇f(x_t))` started in `C`
satisfies `min_{t=0,…,T−1} ‖G^η(x_t)‖ ≤ √(2β(f(x₀) − f(x*)))/√T` for every `T ≥ 1`, where
`G^η(x) = (1/η)(x − P_C(x − η∇f(x)))` with `η = 1/β` is the gradient mapping (55). -/
theorem beck_projected_gradient_rate {ι : Type*} [Fintype ι]
    (C : Set (EuclideanSpace ℝ ι)) (hCne : C.Nonempty) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (f : EuclideanSpace ℝ ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hdiff : ∀ x ∈ C, DifferentiableAt ℝ f x)
    (hsmooth : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (xstar : EuclideanSpace ℝ ι) (hxstar : xstar ∈ C) (hmin : ∀ y ∈ C, f xstar ≤ f y)
    (Proj : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hProj : IsProjOnto C Proj)
    (x : ℕ → EuclideanSpace ℝ ι) (hx0 : x 0 ∈ C)
    (hrun : ∀ t : ℕ, x (t + 1) = Proj (x t - (1 / β) • gradient f (x t))) :
    ∀ T : ℕ, 0 < T → ∃ t < T,
      ‖β • (x t - Proj (x t - (1 / β) • gradient f (x t)))‖ ≤
        Real.sqrt (2 * β * (f (x 0) - f xstar)) / Real.sqrt (T : ℝ) := by sorry

end PolicyGradTheory.ProjGA
