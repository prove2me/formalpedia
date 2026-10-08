-- Prove2me | Theorems.Thm_VarianceRegularization_Covering_two_sided_variance_bound
-- name    : VarianceRegularization.Covering.two_sided_variance_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:40:53.450009+00:00
-- url     : https://prove2.me/theorems/f2ab13e3-a9c6-46d9-9a56-3228182fe551
-- title:
--   Theorem 1, (10) — the robust mean is within 2Mρ/n of the mean plus the standard-deviation penalty
-- statement:
--   Let $n \ge 1$, $\rho \ge 0$, $M_0 \le M_1$ and $M = M_1 - M_0$. Let $z \in [M_0, M_1]^n$, with sample mean $\overline z$ and sample variance $s_n^2 = \frac1n\sum_i z_i^2 - \overline z^{\,2}$, and let $\mathcal P_n$ be the $\chi^2$ ball of radius $\rho$ (weight vectors $p \ge 0$, $\sum_i p_i = 1$, $\frac12 \sum_i (np_i-1)^2 \le \rho$). Then
--   $$
--   \left( \sqrt{\frac{2\rho}{n} s_n^2} - \frac{2M\rho}{n} \right)_+ \;\le\; \sup_{p \in \mathcal P_n} \sum_{i=1}^n p_i z_i - \overline z \;\le\; \sqrt{\frac{2\rho}{n} s_n^2}.
--   $$
--
--   The bound is deterministic: applied to a sample $Z_1, \dots, Z_n$ of a random variable with values in $[M_0, M_1]$ it holds for every realisation. It says that the $\chi^2$-robust risk is the empirical risk plus a standard-deviation penalty, up to an error of $2M\rho/n$, and both halves are used in the proof of Theorem 3.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 7, Theorem 1, inequality (10)

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup

namespace VarianceRegularization.Covering

/-- Theorem 1, inequality (10) (Duchi–Namkoong, arXiv:1610.02581v3, p. 7): for every vector
`z ∈ [M₀, M₁]ⁿ`, `n ≥ 1`, `ρ ≥ 0`, with `M = M₁ - M₀`,
`(√(2ρ s_n²/n) - 2Mρ/n)₊ ≤ sup_{p ∈ 𝒫ₙ} ⟨p, z⟩ - z̄ ≤ √(2ρ s_n²/n)`.
The bound is deterministic: it holds for every realisation of the sample. -/
theorem two_sided_variance_bound (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (M0 M1 : ℝ)
    (hM : M0 ≤ M1) (z : Fin n → ℝ) (hz : ∀ i, z i ∈ Set.Icc M0 M1) :
    max (Real.sqrt (2 * ρ / n * sampleVar z) - 2 * (M1 - M0) * ρ / n) 0
        ≤ VarianceRegularization.Expansion.robustSup n ρ z - VarianceRegularization.Expansion.empMean z ∧
      VarianceRegularization.Expansion.robustSup n ρ z - VarianceRegularization.Expansion.empMean z ≤ Real.sqrt (2 * ρ / n * sampleVar z) := by sorry

end VarianceRegularization.Covering
