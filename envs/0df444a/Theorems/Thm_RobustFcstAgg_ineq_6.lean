-- Prove2me | Theorems.Thm_RobustFcstAgg_ineq_6
-- name    : RobustFcstAgg.ineq_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:59:18.380648+00:00
-- url     : https://prove2.me/theorems/0308c7ae-2ecc-4a72-a4cf-8fa049f7b009
-- title:
--   Inequality (6) (corrected: lower bound for $d^2\le n-1$) — two-sided bound on $\min_{\mathcal A^{\mathrm{lin}}_d}\mathrm{error}$
-- statement:
--   Let $n\ge2$ and $q(n)=\frac{\sqrt n+1}{\sqrt n-1}$. The minimum exists and satisfies
--   $$\min_{A\in\mathcal A^{\mathrm{lin}}_d}\mathrm{error}(A)\le\frac{4}{(q(n)^d+q(n)^{-d})^2},$$
--   and, if $d^2\le n-1$,
--   $$\frac{4\bigl(1-\frac{d^2}{n-1}\bigr)^2}{(q(n)^d+q(n)^{-d})^2}\le\min_{A\in\mathcal A^{\mathrm{lin}}_d}\mathrm{error}(A).$$
--
--   The asymptotics of Theorem 4 are read off from these two explicit bounds.
--
--   Differences from the source:
--   - correction: the lower bound of (6) is printed with no condition on d → the lower bound assumes d² ≤ n − 1; reason: at n = 5, d = 3 the printed left side is 25/1296, which exceeds the printed right side 1/81, since q³ + q⁻³ = 18; p.30 states the condition
--   - encoding: n unrestricted in q(n) and d²/(n−1) → 2 ≤ n; reason: those expressions are undefined at n = 1
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
--   - encoding: the minimum is a real number → ∃ v : ℝ, 0 ≤ v, with ENNReal.ofReal v the least element of the error set; reason: the error is valued in ℝ≥0∞; 0 ≤ v stops ofReal from hiding a negative value
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Inequality (6), p.17

import Mathlib
import Definitions.Def_RobustFcstAgg_linErrorSet
import Definitions.Def_RobustFcstAgg_qn

namespace RobustFcstAgg

/-- **Inequality (6) (corrected: lower bound for `d² ≤ n − 1`).** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Inequality (6), p.17:
`4(1 − d²/(n−1))²/(q(n)^d + q(n)^{−d})² ≤ min_{A ∈ A^lin_d} error(A) ≤ 4/(q(n)^d + q(n)^{−d})²`.

**Formalization Note.** As printed the left side exceeds the right at `n = 5`, `d = 3` (`25/1296` against `1/81`, since
`q³ + q⁻³ = 18`). The condition `d² ≤ n − 1` is the one on p.30. `n ≥ 2`, since `q(1)` is undefined. -/
theorem ineq_6 (n d : ℕ) (hn : 2 ≤ n) :
    ∃ v : ℝ, 0 ≤ v ∧ IsLeast (linErrorSet n d) (ENNReal.ofReal v) ∧
      v ≤ 4 / (qn n ^ d + (qn n ^ d)⁻¹) ^ 2 ∧
      ((d : ℝ) ^ 2 ≤ (n : ℝ) - 1 →
        4 * (1 - (d : ℝ) ^ 2 / ((n : ℝ) - 1)) ^ 2 / (qn n ^ d + (qn n ^ d)⁻¹) ^ 2 ≤ v) := by sorry

end RobustFcstAgg
