-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_convex_iff_dirDeriv_monotone
-- name    : ShorNonsmooth.Subdiff.convex_iff_dirDeriv_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:27:43.152967+00:00
-- url     : https://prove2.me/theorems/ada6d038-17fd-4f83-8c82-9a2bebc3c805
-- title:
--   Theorem 1.9 — convexity iff directional derivatives exist and are nondecreasing along lines
-- statement:
--   A function $f : E_n \to \mathbb{R}$ is convex if and only if its one-sided directional derivative $f'_\eta(x)$ exists (and is finite) at every point $x$ in every direction $\eta$, and for every $x$ and $\eta$ the function
--
--   $$
--   t \longmapsto f'_\eta(x + t\eta), \qquad t \in \mathbb{R},
--   $$
--
--   is nondecreasing.
--
--   This characterizes convexity through monotonicity of one-sided derivatives along lines, and yields the smooth Hessian criterion as a special case.
--
--   **Formalization Note** The derivative is packaged as a function $D(x,\eta)$ with $D(x,\eta) = f'_\eta(x)$ for all $x, \eta$; it is unique because a limit from the right is unique. Existence is required for all directions, including $-\eta$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 11, Theorem 1.9

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_DirDeriv

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 11, Theorem 1.9: a function `f` on `E_n` is convex if and only if its
one-sided directional derivative `f′_η(x)` exists (finite) at every point `x` in every direction
`η`, and `t ↦ f′_η(x + tη)` is nondecreasing for every `x` and `η`. The derivative is recorded as
a function `D x η`; it is unique because the limit from the right is unique. -/
theorem convex_iff_dirDeriv_monotone {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ConvexOn ℝ Set.univ f ↔
      ∃ D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x η, HasOneSidedDirDeriv f x η (D x η)) ∧
          ∀ x η, Monotone (fun t : ℝ => D (x + t • η) η) := by sorry

end ShorNonsmooth.Subdiff
