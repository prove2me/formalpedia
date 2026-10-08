-- Prove2me | Theorems.Thm_VarianceRegularization_Expansion_two_sided_bound
-- name    : VarianceRegularization.Expansion.two_sided_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:53:30.523154+00:00
-- url     : https://prove2.me/theorems/65279873-2dff-4bb9-b2b3-1a62dd76b75c
-- title:
--   Theorem 1, (10): two-sided variance approximation
-- statement:
--   Let $n\ge1$, $\rho\ge0$, and let $z_1,\ldots,z_n$ lie in $[M_0,M_1]$ with $M=M_1-M_0$. If $\bar z$ and $s_n^2$ are their empirical mean and variance, then
--
--   $$\left(\sqrt{\frac{2\rho s_n^2}{n}}-\frac{2M\rho}{n}\right)_+\le R_n(z,\rho)-\bar z\le\sqrt{\frac{2\rho s_n^2}{n}}.$$
--
--   This is the deterministic finite-sample guarantee even when the exact expansion condition fails.
--
--   **Formalization Note** The positive part is `max · 0`; each sample coordinate is constrained to the stated interval.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 7, Theorem 1, inequality (10)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_robustSup
import Definitions.Def_VarianceRegularization_Expansion_empVar

namespace VarianceRegularization.Expansion

/-- Theorem 1, inequality (10), p. 7: deterministic two-sided approximation. -/
theorem two_sided_bound {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁) :
    max (Real.sqrt (2 * ρ / (n : ℝ) * empVar z) -
        2 * (M₁ - M₀) * ρ / (n : ℝ)) 0 ≤
      robustSup n ρ z - empMean z ∧
    robustSup n ρ z - empMean z ≤
      Real.sqrt (2 * ρ / (n : ℝ) * empVar z) := by sorry

end VarianceRegularization.Expansion
