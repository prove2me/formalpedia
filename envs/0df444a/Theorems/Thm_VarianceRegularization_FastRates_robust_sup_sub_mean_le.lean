-- Prove2me | Theorems.Thm_VarianceRegularization_FastRates_robust_sup_sub_mean_le
-- name    : VarianceRegularization.FastRates.robust_sup_sub_mean_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:38.446806+00:00
-- url     : https://prove2.me/theorems/918b6c54-7c93-4ea9-b6b5-16fa05ecb369
-- title:
--   Theorem 1, (10) upper half — the robust value exceeds the empirical mean by at most $\sqrt{2\rho s_n^2/n}$
-- statement:
--   Let $n\ge1$, $\rho\ge0$, and let $z\in\mathbb R^n$ be a vector of sample values with empirical mean $\bar z=\frac1n\sum_i z_i$ and empirical variance $s_n^2=\frac1n\sum_i z_i^2-\bar z^2$. Then
--   $$\sup_{p\in\mathcal P_n}\sum_{i=1}^n p_i z_i-\bar z\ \le\ \sqrt{\frac{2\rho}{n}s_n^2},$$
--   where $\mathcal P_n=\{p\in\mathbb R^n_+:\frac12\|np-\mathbf 1\|_2^2\le\rho,\ \langle\mathbf 1,p\rangle=1\}$ is the $\chi^2$ ball (8).
--
--   This is the upper half of the paper's inequality (10). It says that the robust risk is never more than a standard-deviation penalty above the empirical risk, and in the fast-rate argument it converts a gap in robust risks into a gap in empirical means plus a variance term.
--
--   **Formalization Note** Only the upper bound of (10) is stated; it is the half used in the proof of Theorem 5 (p. 46). It holds for every real vector, so the boundedness assumption $Z\in[M_0,M_1]$ of Theorem 1 (needed only for the lower bound) is not imposed.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 7, Theorem 1, inequality (10) (upper bound)

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk

namespace VarianceRegularization.FastRates

/-- Duchi–Namkoong, arXiv:1610.02581v3, p. 7, Theorem 1, upper half of inequality (10): for every
vector of sample values `z ∈ ℝⁿ` (the theorem's `Z` taking values in a bounded interval is not used
by this half), `sup_{p ∈ 𝒫_n} ⟨p, z⟩ − 𝔼_{P̂_n}[Z] ≤ √(2ρ s_n² / n)`. Stated on the weight-vector
form (8) of the χ² ball. -/
theorem robust_sup_sub_mean_le (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (z : Fin n → ℝ) :
    VarianceRegularization.Expansion.robustSup n ρ z - VarianceRegularization.Expansion.empMean z ≤ Real.sqrt (2 * ρ / n * empVar z) := by sorry

end VarianceRegularization.FastRates
