-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_valueFn_convexOn
-- name    : ShorNonsmooth.Decomposition.valueFn_convexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:22:06.45068+00:00
-- url     : https://prove2.me/theorems/80effeb9-cbda-45b4-a52c-566e4db4387f
-- title:
--   Theorem 4.1 (first part) — the value function $\Phi$ is convex where it is defined
-- statement:
--   Let $f_0$ and $f_i$, $i = 1,\dots,n$, be jointly convex functions of $(x,y) \in E^x_l \times E^y_m$, let $D(x) = \{y : f_i(x,y) \le 0 \text{ for all } i\}$, and let $\Phi(x) = \min_{y \in D(x)} f_0(x,y)$ be the value function (4.5). If $W \subseteq E^x_l$ is convex and the minimum defining $\Phi(x)$ is attained for every $x \in W$, then
--   $$
--   \Phi(\lambda_1 x_1 + \lambda_2 x_2) \le \lambda_1 \Phi(x_1) + \lambda_2 \Phi(x_2) \qquad (x_1,x_2 \in W,\ \lambda_1,\lambda_2 \ge 0,\ \lambda_1+\lambda_2 = 1),
--   $$
--   that is, $\Phi$ is convex on $W$.
--
--   This is the convexity half of Theorem 4.1: minimizing a jointly convex program over one block of variables leaves a convex problem in the other block, which is what makes decomposition with respect to variables a convex minimization of $\Phi$.
--
--   **Formalization Note** The book says "convex on some convex subset $W$ of $E_n$"; $E_n$ is read as the $x$-space and $W$ as any convex set on which $\Phi$ is defined (the minimum is attained).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 94, Theorem 4.1 (first sentence); proof pp. 94–95

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), Theorem 4.1, first assertion (p. 94; proof p. 94–95): if `f₀` and all `f_i` are
jointly convex, then the value function `Φ(x) = min_{y ∈ D(x)} f₀(x, y)` of (4.5) is convex on every
convex set `W` of `x`-values at which the minimum in (4.5) is attained. (The book's "some convex subset
`W` of `E_n`" is read as: any convex subset of `E^x_l` on which `Φ` is defined.) -/
theorem valueFn_convexOn {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x) :
    ConvexOn ℝ W (valueFn f₀ f) := by sorry

end ShorNonsmooth.Decomposition
