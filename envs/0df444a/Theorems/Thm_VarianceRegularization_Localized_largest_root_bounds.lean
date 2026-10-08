-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_largest_root_bounds
-- name    : VarianceRegularization.Localized.largest_root_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:34.445609+00:00
-- url     : https://prove2.me/theorems/39e559a0-d93e-468f-9094-5248a162b9c2
-- title:
--   Lemma D.4 — bounds on the largest root of ax + b = x²/d
-- statement:
--   Let $a,b,d>0$ and let $x$ be the largest solution of
--   $$
--   ax+b=\frac{x^2}{d}.
--   $$
--   Then
--   $$
--   a^2d^2\ \le\ x^2\ \le\ a^2d^2+2bd .
--   $$
--
--   The lemma fixes the localization radius in the proofs of Lemmas D.2 and D.3, where the radius is chosen as the largest root of such an equation.
--
--   **Formalization Note** For $a,b,d>0$ the quadratic $x^2-adx-bd=0$ has one negative and one positive root, so the largest solution is the unique nonnegative one; the statement is made for every nonnegative solution $x$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 42, Lemma D.4

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Lemma D.4** (p. 42). Let `x` be the largest solution to `a x + b = x² / d` where
`a, b, d > 0`. Then `a² d² ≤ x² ≤ a² d² + 2 b d`.

For `a, b, d > 0` the quadratic `x² − a d x − b d = 0` has one negative and one positive root, so
"the largest solution" is exactly the unique nonnegative solution; the statement takes any
nonnegative `x` solving the equation. -/
theorem largest_root_bounds (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hx : 0 ≤ x)
    (heq : a * x + b = x ^ 2 / d) :
    a ^ 2 * d ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ a ^ 2 * d ^ 2 + 2 * b * d := by sorry

end VarianceRegularization.Localized
