-- Prove2me | Theorems.Thm_Rudin_ch06_monotonicity_and_bounds_of_bounded
-- name    : Rudin.ch06_monotonicity_and_bounds_of_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:19:05.371386+00:00
-- url     : https://prove2.me/theorems/3df79e1d-c55b-49c4-84df-7921070422f3
-- title:
--   Monotonicity, additivity and bounds for the Riemann-Stieltjes integral (Rudin 6.12 b,c,d), corrected
-- statement:
--   **Basic properties of the Riemann–Stieltjes integral.** Let $\alpha$ be monotonically increasing on $[a,b]$ and let $f, g \in \mathcal{R}(\alpha)$ on $[a,b]$, both bounded. Then:
--
--   1. *(Monotonicity.)* If $f(x) \le g(x)$ on $[a,b]$, then $\displaystyle\int_a^b f\,d\alpha \le \int_a^b g\,d\alpha$.
--   2. *(Additivity over adjacent intervals.)* For every $c \in [a,b]$, $f \in \mathcal{R}(\alpha)$ on $[a,c]$ and on $[c,b]$, and
--   $$\int_a^c f\,d\alpha + \int_c^b f\,d\alpha \;=\; \int_a^b f\,d\alpha.$$
--   3. *(Bound.)* If $|f(x)| \le M$ on $[a,b]$, then $\left|\int_a^b f\,d\alpha\right| \le M\,(\alpha(b) - \alpha(a))$.
--
--   These are parts (b), (c) and (d) of Rudin's Theorem 6.12.
--
--   **Formalization note.** Boundedness is part of Rudin's standing setup in Chapter 6 — his $\mathcal{R}(\alpha)$ consists of bounded functions — and it must be stated explicitly here. Upper and lower sums are built from `sSup` and `sInf`, which return the junk value $0$ on sets that are unbounded, so an unbounded function can satisfy the formal integrability predicate with integral $0$. On $[0,1]$ with $\alpha = \mathrm{id}$, take $f(0) = -1$ and $f(x) = -1/x$ for $x \neq 0$: every upper sum set is unbounded below and every lower sum is $\le 0$ with the value $0$ attained at the trivial partition, so both the upper and the lower integral come out $0$. With $g \equiv -1$ one has $f \le g$ on $[0,1]$ while part 1 would demand $0 \le -1$. The two boundedness hypotheses match those already carried by `Rudin.ch06_linearity`.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 6, Theorem 6.12(b),(c),(d), pp. 128-129. Corrected form of the platform theorem Rudin.ch06_monotonicity_and_bounds.

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(b), (c), (d), with the boundedness hypotheses of Chapter 6: the integral
is monotone in the integrand, additive over adjacent intervals, and bounded by `M (α b - α a)`
when `|f| ≤ M`. -/
theorem ch06_monotonicity_and_bounds_of_bounded (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    ((∀ x ∈ Set.Icc a b, f x ≤ g x) → RSIntegral a b f α ≤ RSIntegral a b g α) ∧
    (∀ c ∈ Set.Icc a b, RSIntegrable a c f α ∧ RSIntegrable c b f α ∧
      RSIntegral a c f α + RSIntegral c b f α = RSIntegral a b f α) ∧
    (∀ M : ℝ, (∀ x ∈ Set.Icc a b, |f x| ≤ M) →
      |RSIntegral a b f α| ≤ M * (α b - α a)) := by sorry

end Rudin
