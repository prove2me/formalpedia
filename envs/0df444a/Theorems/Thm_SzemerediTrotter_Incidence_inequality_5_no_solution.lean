-- Prove2me | Theorems.Thm_SzemerediTrotter_Incidence_inequality_5_no_solution
-- name    : SzemerediTrotter.Incidence.inequality_5_no_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T11:02:29.110641+00:00
-- url     : https://prove2.me/theorems/6aa85248-7ff7-4271-8727-34aa293c9344
-- title:
--   Section 3, inequality (5) — no solution in $(0,.1]$, a solution in $(.1,.2)$
-- statement:
--   Consider the function
--
--   $$f(x) = x^{2/3} + \frac{1-x}{100} + 2^{-1/3}(1-x)^{2/3}.$$
--
--   1. For every real $x$ with $0 < x \le 0.1$ one has $f(x) \le 1$; that is, inequality (5) of Szemerédi and Trotter, $1 < f(x_0)$, has no solution in the interval $(0, 0.1]$.
--   2. There is a real $x$ with $0.1 < x < 0.2$ and $1 < f(x)$; that is, inequality (5) does have a solution in $(0.1, 0.2)$.
--
--   In the proof of Theorem 1 the first part shows that the set $\mathcal P_0$ of points incident with many lines from both halves of the slope-ordered family has at least a tenth of the points. The second part is the paper's parenthetical remark that the threshold $0.1$ cannot be raised to $0.2$ by this inequality alone.
--
--   **Formalization Note** All powers are `Real.rpow` with real exponents $2/3$ and $-1/3$; on the stated ranges all bases are positive.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 385, Section 3, inequality (5) and the sentence following it (printed as "inequality (2)", a misprint for (5))

import Mathlib

namespace SzemerediTrotter.Incidence

/-- Section 3, inequality (5), p. 385: `1 < x₀^{2/3} + (1 − x₀)/100 + 2^{−1/3}(1 − x₀)^{2/3}`
has no solution in `(0, .1]`, and it has a solution in `(.1, .2)`. -/
theorem inequality_5_no_solution :
    (∀ x : ℝ, 0 < x → x ≤ 0.1 →
      x ^ (2 / 3 : ℝ) + (1 - x) / 100 + (2 : ℝ) ^ (-(1 / 3) : ℝ) * (1 - x) ^ (2 / 3 : ℝ) ≤ 1) ∧
    (∃ x : ℝ, 0.1 < x ∧ x < 0.2 ∧
      1 < x ^ (2 / 3 : ℝ) + (1 - x) / 100 + (2 : ℝ) ^ (-(1 / 3) : ℝ) * (1 - x) ^ (2 / 3 : ℝ)) := by sorry

end SzemerediTrotter.Incidence
