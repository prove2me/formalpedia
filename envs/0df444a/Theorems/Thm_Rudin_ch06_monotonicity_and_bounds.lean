-- Prove2me | Theorems.Thm_Rudin_ch06_monotonicity_and_bounds
-- name    : Rudin.ch06_monotonicity_and_bounds
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T23:21:05.425984+00:00
-- url     : https://prove2.me/theorems/c630587a-f124-473a-80fd-b964450fa383
-- title:
--   Theorem 6.12(b,c,d) — monotonicity, additivity in the interval, and the basic bound
-- statement:
--   For $f, g \in \mathcal{R}(\alpha)$ on $[a,b]$: if $f \le g$ on $[a,b]$ then $\int f\,d\alpha \le \int g\,d\alpha$; for $c \in [a,b]$, $f$ is integrable on $[a,c]$ and on $[c,b]$ and the two integrals add up to the integral over $[a,b]$; and if $|f| \le M$ then $\left|\int_a^b f\,d\alpha\right| \le M(\alpha(b) - \alpha(a))$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 128, Theorem 6.12(b), (c), (d)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(b), (c), (d): the integral is monotone in the integrand, additive over
adjacent intervals, and bounded by `M (α b - α a)` when `|f| ≤ M`. -/
theorem ch06_monotonicity_and_bounds (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α) :
    ((∀ x ∈ Set.Icc a b, f x ≤ g x) → RSIntegral a b f α ≤ RSIntegral a b g α) ∧
    (∀ c ∈ Set.Icc a b, RSIntegrable a c f α ∧ RSIntegrable c b f α ∧
      RSIntegral a c f α + RSIntegral c b f α = RSIntegral a b f α) ∧
    (∀ M : ℝ, (∀ x ∈ Set.Icc a b, |f x| ≤ M) →
      |RSIntegral a b f α| ≤ M * (α b - α a)) := by sorry

end Rudin
