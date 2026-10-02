-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_neg_minNorm_subgradient_steepest_descent
-- name    : ShorNonsmooth.Subdiff.neg_minNorm_subgradient_steepest_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:24:46.797824+00:00
-- url     : https://prove2.me/theorems/f93bd79d-5c15-474e-b037-89196a407689
-- title:
--   Theorem 1.11 — minus the minimal-norm subgradient is a direction of steepest descent
-- statement:
--   Let $M \subseteq E_n$, let $f$ be convex on $M$, and let $x_0$ be an interior point of $M$ with $0 \notin G(x_0)$. Let $g_0$ be the element of $G(x_0)$ nearest to the origin, i.e. $g_0 \in G(x_0)$ and $\|g_0\| \le \|g\|$ for every $g \in G(x_0)$. Then $-g_0$ is a direction of steepest descent of $f$ at $x_0$:
--
--   $$
--   \min_{\|\xi\|=1} f'_\xi(x_0) = \frac{1}{\|g_0\|}\, f'_{-g_0}(x_0).
--   $$
--
--   This result underlies descent methods that move against the shortest subgradient.
--
--   **Formalization Note** The printed statement says that the minimal-norm element $\eta$ of $G(x_0)$ is itself a direction of steepest descent, which is false (along it the directional derivative is $\max_{g} (g, \eta) \ge \|\eta\|^2 > 0$). The book's proof takes $\eta$ as the common boundary point of the ball $\{\|x\| \le \|\eta\|\}$ and $-G(x_0)$ and obtains $f'_\eta(x_0) = -(\eta,\eta)$, and the remark after the proof ("$-\eta$ is equal to the gradient") confirms the intended direction is minus the minimal-norm subgradient. The theorem stated here is the one the proof establishes.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 12, Theorem 1.11 (sign corrected per its proof)

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Definitions.Def_ShorNonsmooth_Subdiff_DirDeriv

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 12, Theorem 1.11, **as proved** (the printed statement has a sign slip): let
`f` be convex with domain `M`, `x₀` an interior point of `M`, `0 ∉ G(x₀)`, and let `g₀` be the
element of `G(x₀)` nearest to the origin. Then `-g₀` is a direction of steepest descent of `f` at
`x₀`. The book writes "`η` is the element of `G(x₀)` nearest to the origin … `η` is a direction of
steepest descent", but its proof takes `η` as the common boundary point of the ball
`‖x‖ ≤ ‖η‖` and `-G(x₀)` and computes `f′_η(x₀) = -(η, η) < 0`; the remark after the proof
("`-η` is equal to the gradient") confirms `η = -g₀`. Along `g₀` itself `f′_{g₀}(x₀) > 0`. -/
theorem neg_minNorm_subgradient_steepest_descent {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ M f) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ subdifferential M f x₀)
    (g₀ : EuclideanSpace ℝ (Fin n)) (hg₀ : g₀ ∈ subdifferential M f x₀)
    (hmin : ∀ g ∈ subdifferential M f x₀, ‖g₀‖ ≤ ‖g‖) :
    IsSteepestDescentDir f x₀ (-g₀) := by sorry

end ShorNonsmooth.Subdiff
