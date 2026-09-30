-- Prove2me | Theorems.Thm_SzemerediTrotter_Incidence_inequality_1_no_solution
-- name    : SzemerediTrotter.Incidence.inequality_1_no_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:58:09.051802+00:00
-- url     : https://prove2.me/theorems/a55ef5cd-c3d4-4f13-a427-7995f91a3a43
-- title:
--   Section 3, inequality (1) — $.6x_1 + (1-x_1)^{2/3} > 1$ has no solution in $0 < x_1 \le 1/2$
-- statement:
--   For every real number $x$ with $0 < x \le \tfrac12$,
--
--   $$0.6\,x + (1-x)^{2/3} \le 1.$$
--
--   Equivalently, inequality (1) of Szemerédi and Trotter, $0.6\,x_1 + (1-x_1)^{2/3} > 1$, has no solution in the range $0 < x_1 \le 1/2$. In the proof of Theorem 1 this rules out a positive fraction of lines of low density (and, by the same argument, of points of low degree) in a minimal counterexample.
--
--   **Formalization Note** The power $(1-x)^{2/3}$ is the real power `Real.rpow` with exponent the real number $2/3$; on the stated range the base $1-x$ is in $[1/2, 1)$, so no convention for negative bases is involved.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 384, Section 3, inequality (1)

import Mathlib

namespace SzemerediTrotter.Incidence

/-- Section 3, inequality (1), p. 384: `.6x₁ + (1 − x₁)^{2/3} > 1` has no solution with
`0 < x₁ ≤ 1/2`. -/
theorem inequality_1_no_solution :
    ∀ x : ℝ, 0 < x → x ≤ 1 / 2 → (0.6 : ℝ) * x + (1 - x) ^ (2 / 3 : ℝ) ≤ 1 := by sorry

end SzemerediTrotter.Incidence
