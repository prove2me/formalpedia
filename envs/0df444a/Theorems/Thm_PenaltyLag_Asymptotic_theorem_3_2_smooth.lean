-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_theorem_3_2_smooth
-- name    : PenaltyLag.Asymptotic.theorem_3_2_smooth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:21.426052+00:00
-- url     : https://prove2.me/theorems/6d5148c1-6606-4632-8e27-4a66be764c4c
-- title:
--   Theorem 3.2 (third and fourth sentences) — if $g_0 \not\equiv -\infty$, $g_r$ is finite, $C^1$, with gradient (3.6)
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Let $r > 0$ and assume $g_0$ is not identically $-\infty$. Then $g_r$ is finite everywhere and continuously differentiable on $\mathbb R^m$. Moreover, if for a given $y$ the infimum defining $g_r(y)$ is attained at a point $x \in X$ (not necessarily unique), then for $i = 1, \dots, m$
--   $$
--   \frac{\partial g_r(y)}{\partial y_i} = \frac{\partial L_r(x, y)}{\partial y_i} = \frac{\theta(y_i + 2 r f_i(x)) - y_i}{2r} = \max\Big\{-\frac{y_i}{2r},\ f_i(x)\Big\}. \tag{3.6}
--   $$
--
--   This is what allows $(D_r)$ to be attacked by unconstrained smooth maximization, with gradients computed from approximate minimizers of $L_r(\cdot, y)$.
--
--   **Formalization Note** The first equality of (3.6) is stated as equality of the gradients $\nabla g_r(y) = \nabla_y L_r(x, y)$ in $\mathbb R^m$ (Euclidean space, so the gradient's coordinates are the partial derivatives); the other two are stated coordinatewise. Since $g_r$ is `EReal`-valued, finiteness is a separate conclusion and differentiability is stated for its real coercion `grR`, which agrees with $g_r$ by that conclusion. "The infimum is attained at $x$" is $x \in X$ with $L_r(x, y) = g_r(y)$. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 359, Theorem 3.2 (third and fourth sentences), (3.6)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Theorem 3.2, third and fourth sentences (p. 359): if g₀ ≢ −∞ and r > 0, g_r is finite and
C¹ on ℝ^m, and at a point x ∈ X attaining the infimum defining g_r(y) the gradient formula (3.6)
holds. -/
theorem theorem_3_2_smooth {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (hg0 : ∃ z : Mult m, g0 X f₀ f z ≠ ⊥) :
    (∀ y : Mult m, gr X f₀ f r y ≠ ⊥ ∧ gr X f₀ f r y ≠ ⊤) ∧
    ContDiff ℝ 1 (grR X f₀ f r) ∧
    ∀ y : Mult m, ∀ x ∈ X, (Lr f₀ f r x y : EReal) = gr X f₀ f r y →
      gradient (grR X f₀ f r) y = gradient (fun y' : Mult m => Lr f₀ f r x y') y ∧
      ∀ i : Fin m,
        (gradient (fun y' : Mult m => Lr f₀ f r x y') y) i
            = (theta (y i + 2 * r * f i x) - y i) / (2 * r) ∧
        (theta (y i + 2 * r * f i x) - y i) / (2 * r) = max (-(y i) / (2 * r)) (f i x) := by sorry

end PenaltyLag.Asymptotic
