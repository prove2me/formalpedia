-- Prove2me | Theorems.Thm_SAGA_StronglyConvex_lemma4_strongly_convex_smooth_lower_bound
-- name    : SAGA.StronglyConvex.lemma4_strongly_convex_smooth_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:54:10.916782+00:00
-- url     : https://prove2.me/theorems/c7496b53-45c4-448a-9ace-9fa4600db0b7
-- title:
--   Lemma 4 — lower bound for strongly convex functions with Lipschitz gradient (for $\mu<L$)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with gradient $f'$, $\mu$-strongly convex ($\mu>0$), and let $f'$ be Lipschitz continuous with constant $L$, where $\mu<L$. Then for all $x,y\in\mathbb R^d$,
--
--   $$
--   f(x)\;\ge\; f(y)+\langle f'(y),x-y\rangle+\frac{1}{2(L-\mu)}\|f'(x)-f'(y)\|^2+\frac{\mu L}{2(L-\mu)}\|y-x\|^2+\frac{\mu}{L-\mu}\langle f'(x)-f'(y),y-x\rangle .
--   $$
--
--   This interpolates between the strong-convexity lower bound and the co-coercivity of the gradient. It is the only place where strong convexity and smoothness are combined in the linear-rate analysis; Lemma 1 follows from it by averaging over the components.
--
--   **Formalization Note** The paper does not state $\mu<L$, but the fractions $1/(L-\mu)$ require it; without it, Lean's convention $a/0=0$ would turn the statement into plain convexity at $\mu=L$. Strong convexity is Mathlib's `StrongConvexOn Set.univ μ f`, whose modulus $\frac\mu2\|x-y\|^2$ is the paper's convention. The space is `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 10, Appendix B, Lemma 4

import Mathlib

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Lemma 4 (Appendix B, p. 10). `f` is `μ`-strongly convex with `L`-Lipschitz gradient `f'`.
The page leaves `μ < L` implicit; the fractions `1/(L-μ)` require it, so it is a hypothesis. -/
theorem lemma4_strongly_convex_smooth_lower_bound {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (f' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ L : ℝ) (hμ : 0 < μ) (hμL : μ < L)
    (hgrad : ∀ x, HasGradientAt f (f' x) x)
    (hsc : StrongConvexOn Set.univ μ f)
    (hlip : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin d)) :
    f y + ⟪f' y, x - y⟫_ℝ + 1 / (2 * (L - μ)) * ‖f' x - f' y‖ ^ 2
      + μ * L / (2 * (L - μ)) * ‖y - x‖ ^ 2 + μ / (L - μ) * ⟪f' x - f' y, y - x⟫_ℝ ≤ f x := by sorry

end SAGA.StronglyConvex
