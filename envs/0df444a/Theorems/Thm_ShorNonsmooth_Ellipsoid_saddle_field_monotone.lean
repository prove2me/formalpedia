-- Prove2me | Theorems.Thm_ShorNonsmooth_Ellipsoid_saddle_field_monotone
-- name    : ShorNonsmooth.Ellipsoid.saddle_field_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:19:32.545163+00:00
-- url     : https://prove2.me/theorems/8efa2586-6cea-4b8d-89a6-49ea592a01ca
-- title:
--   p. 90 — the pseudo-gradient field of a convex–concave saddle point problem
-- statement:
--   Let $f(x, y)$ be a function of $x \in E_n$ and $y \in E_m$ that is convex in $x$ for fixed $y$ and concave in $y$ for fixed $x$, and let $z^* = \{x^*, y^*\}$ be a saddle point:
--   $$
--   f(x^*, y) \le f(x^*, y^*) \le f(x, y^*) \qquad \text{for all } x, y .
--   $$
--   For every $z = \{x, y\}$ let $g_f^x(z)$ be a partial subgradient of $f(\cdot, y)$ at $x$, and let $g_f^y(z)$ be such that $-g_f^y(z)$ is a subgradient of $-f(x, \cdot)$ at $y$. Put $g(z) = \{g_f^x(z), -g_f^y(z)\} \in E_n \times E_m = E_{n+m}$. Then
--   $$
--   (g(z), z - z^*) \ge 0 \qquad \text{for all } z \in E_{n+m}.
--   $$
--
--   Hence the algorithm (3.57)–(3.60), run in $E_{n+m}$ on the field $g$, localizes a saddle point.
--
--   **Formalization Note** The inner product of $E_{n+m} = E_n \times E_m$ is written as the sum $(g_f^x(z), x - x^*) + (-g_f^y(z), y - y^*)$ of the inner products of the two blocks. The partial supergradient condition is $f(x, y') - f(x, y) \le (g_f^y(x, y), y' - y)$ for all $y'$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 90, §3.8.3 (The Saddle Point Problem), unnumbered display

import Mathlib

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), p. 90, §3.8.3 (the saddle point problem). Let `f(x, y)` be convex in
`x ∈ E_n` for fixed `y` and concave in `y ∈ E_m` for fixed `x`, with a saddle point
`z* = (x*, y*)`: `f(x*, y) ≤ f(x*, y*) ≤ f(x, y*)`. Let `g_f^x(x, y)` be a partial subgradient of
`f(·, y)` at `x` and `g_f^y(x, y)` a partial supergradient of `f(x, ·)` at `y` (so `-g_f^y` is a
subgradient of `-f(x, ·)`), and `g(z) = {g_f^x(z), -g_f^y(z)}`. Then `(g(z), z - z*) ≥ 0` for all
`z = (x, y) ∈ E_n × E_m = E_{n+m}`; the inner product of `E_{n+m}` is written as the sum of the
inner products of the two blocks. -/
theorem saddle_field_monotone {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hconv : ∀ y, ConvexOn ℝ Set.univ (fun x => f x y))
    (hconc : ∀ x, ConcaveOn ℝ Set.univ (fun y => f x y))
    (gx : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (gy : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hgx : ∀ x y x', f x' y - f x y ≥ inner ℝ (gx x y) (x' - x))
    (hgy : ∀ x y y', f x y' - f x y ≤ inner ℝ (gy x y) (y' - y))
    (xstar : EuclideanSpace ℝ (Fin n)) (ystar : EuclideanSpace ℝ (Fin m))
    (hsaddle : ∀ x y, f xstar y ≤ f xstar ystar ∧ f xstar ystar ≤ f x ystar) :
    ∀ x y, 0 ≤ inner ℝ (gx x y) (x - xstar) + inner ℝ (-gy x y) (y - ystar) := by sorry

end ShorNonsmooth.Ellipsoid
