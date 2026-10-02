-- Prove2me | Theorems.Thm_ShorNonsmooth_Ellipsoid_convex_program_field_monotone
-- name    : ShorNonsmooth.Ellipsoid.convex_program_field_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:19:10.448597+00:00
-- url     : https://prove2.me/theorems/02322a76-133e-4794-9755-36234767aafc
-- title:
--   Eq. (3.65) — a vector field for the general convex programming problem (3.64)
-- statement:
--   Consider the convex program (3.64): minimize $f_0(x)$ subject to $f_i(x) \le 0$, $i = 1, \dots, m$, $x \in E_n$, where $f_0, f_1, \dots, f_m$ are convex functions on $E_n$ with subgradients $g_\nu(x)$, $\nu = 0, 1, \dots, m$. Let $x^*$ be an optimal point. Define
--   $$
--   g(x) = \begin{cases} g_0(x) & \text{if } \max_{1 \le i \le m} f_i(x) \le 0, \\[2pt] g_{i^*}(x) & \text{if } \max_{1 \le i \le m} f_i(x) = f_{i^*}(x) > 0. \end{cases}
--   $$
--   Then
--   $$
--   (g(x), x - x^*) \ge 0 \qquad \text{for all } x \in E_n .
--   $$
--
--   Consequently the algorithm (3.57)–(3.60) localizes an optimal point of any convex program for which a ball containing it is known.
--
--   **Formalization Note** The constraints are indexed by `Fin m` (so $m = 0$, the unconstrained case, is allowed). The field $g$ is any map with $g(x) = g_0(x)$ at feasible points and $g(x) = g_{i^*}(x)$ for some maximizing index $i^*$ at infeasible points; the choice of $i^*$ may depend on $x$ arbitrarily. Optimality of $x^*$ means $x^*$ is feasible and $f_0(x^*) \le f_0(x)$ for every feasible $x$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 89–90, §3.8.2, problem (3.64) and Eq. (3.65)

import Mathlib

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), pp. 89–90, (3.64)–(3.65). Let `f₀, f₁, …, f_m` be convex on `E_n` with
subgradient selections `g₀, g₁, …, g_m`, and let `x*` be an optimal point of
`min f₀(x)` s.t. `fᵢ(x) ≤ 0`, `i = 1, …, m`. Let `g` be the field (3.65):
`g(x) = g₀(x)` if `max_i fᵢ(x) ≤ 0`, and `g(x) = g_{i*}(x)` for an index `i*` with
`max_i fᵢ(x) = f_{i*}(x) > 0` otherwise. Then `(g(x), x - x*) ≥ 0` for all `x ∈ E_n`.
Constraints are indexed by `Fin m`; the maximizing index may depend on `x` arbitrarily. -/
theorem convex_program_field_monotone {n m : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf₀ : ConvexOn ℝ Set.univ f₀) (hf : ∀ i, ConvexOn ℝ Set.univ (f i))
    (g₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (gc : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg₀ : ∀ x y : EuclideanSpace ℝ (Fin n), f₀ y - f₀ x ≥ inner ℝ (g₀ x) (y - x))
    (hgc : ∀ i, ∀ x y : EuclideanSpace ℝ (Fin n), f i y - f i x ≥ inner ℝ (gc i x) (y - x))
    (xstar : EuclideanSpace ℝ (Fin n)) (hfeas : ∀ i, f i xstar ≤ 0)
    (hopt : ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, f i x ≤ 0) → f₀ xstar ≤ f₀ x)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg_feas : ∀ x, (∀ i, f i x ≤ 0) → g x = g₀ x)
    (hg_infeas : ∀ x, (∃ i, 0 < f i x) →
      ∃ istar : Fin m, (∀ j, f j x ≤ f istar x) ∧ g x = gc istar x) :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ (g x) (x - xstar) := by sorry

end ShorNonsmooth.Ellipsoid
