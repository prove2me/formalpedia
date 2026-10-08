-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_theorem_3_2_envelope
-- name    : PenaltyLag.Asymptotic.theorem_3_2_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:22.941435+00:00
-- url     : https://prove2.me/theorems/6d1506cb-8a5a-47f2-84de-a02e36e121bd
-- title:
--   Theorem 3.2 (first sentence) — $g_r$ is concave and $g_r(y) = \max_z \{g_0(z) - \frac{1}{4r}|z-y|^2\}$
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). For every $r > 0$, the function $g_r(y) = \inf_{x \in X} L_r(x, y)$ is concave on $\mathbb R^m$ and satisfies
--   $$
--   g_r(y) = \max_{z \in \mathbb R^m} \Big\{ g_0(z) - \frac{1}{4r}|z - y|^2 \Big\}, \qquad y \in \mathbb R^m, \tag{3.5}
--   $$
--   the maximum being attained.
--
--   So $g_r$ is the upper Moreau envelope of the ordinary dual function $g_0$; this is what makes the penalty dual $(D_r)$ a smooth problem with the same solutions as $(D_0)$.
--
--   **Formalization Note** $g_r$ and $g_0$ take values in $[-\infty, +\infty)$, so concavity is stated as convexity of the hypograph $\{(y, t) \in \mathbb R^m \times \mathbb R : t \le g_r(y)\}$, and "max" as: $g_r(y)$ is the greatest element of the set of values on the right. When $g_0 \equiv -\infty$ both sides are $-\infty$ and every $z$ attains it. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 359, Theorem 3.2 (first sentence), (3.5)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Theorem 3.2, first sentence (p. 359): for r > 0, g_r is concave (its hypograph is convex)
and g_r(y) = max_z {g₀(z) − (1/4r)|z − y|²} (3.5), the maximum being attained. -/
theorem theorem_3_2_envelope {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) :
    Convex ℝ {p : Mult m × ℝ | (p.2 : EReal) ≤ gr X f₀ f r p.1} ∧
    ∀ y : Mult m, IsGreatest
      (Set.range fun z : Mult m => g0 X f₀ f z - (((1 / (4 * r)) * ‖z - y‖ ^ 2 : ℝ) : EReal))
      (gr X f₀ f r y) := by sorry

end PenaltyLag.Asymptotic
