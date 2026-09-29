-- Prove2me | Theorems.Thm_Rudin_ch10_iterated_integral_of_le
-- name    : Rudin.ch10_iterated_integral_of_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:14:02.456381+00:00
-- url     : https://prove2.me/theorems/89e20d9b-b818-4902-addb-173e22efd107
-- title:
--   Order of integration on a 2-cell (Rudin 10.2), corrected
-- statement:
--   **Order of integration on a 2-cell.** Let $a \le b$ and $c \le d$ be reals and let $f$ be continuous on the rectangle $[a,b] \times [c,d]$. Then the two iterated integrals agree:
--   $$\int_a^b\!\!\left(\int_c^d f(x,y)\,dy\right)dx \;=\; \int_c^d\!\!\left(\int_a^b f(x,y)\,dx\right)dy.$$
--
--   This is Rudin's Theorem 10.2, with the orientation hypotheses $a \le b$ and $c \le d$ made explicit.
--
--   **Why the orientation hypotheses are needed in a formal statement.** Lean's $\int_a^b$ is defined for all $a, b$, with $\int_a^b = -\int_b^a$, whereas `Set.Icc a b` is *empty* when $b < a$. So with reversed endpoints the continuity hypothesis can be vacuous while both iterated integrals are still perfectly well defined and genuinely different. Concretely, with $a = 1$, $b = 0$, $c = 0$, $d = 1$ and
--   $$f(x,y) = \frac{x^2 - y^2}{(x^2+y^2)^2},$$
--   the set $[1,0]$ is empty, so the hypothesis holds vacuously, but the classical computation gives $-\pi/4$ on the left and $\pi/4$ on the right. Adding $a \le b$ and $c \le d$ restores Rudin's 2-cell and the theorem.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 10, Theorem 10.2, p. 246. Corrected form of the platform theorem Rudin.ch10_iterated_integral (disproved).

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.2, with the orientation hypotheses `a ≤ b` and `c ≤ d`: for a continuous
function on the 2-cell `[a, b] × [c, d]` the two iterated integrals agree. -/
theorem ch10_iterated_integral_of_le (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by sorry

end Rudin
