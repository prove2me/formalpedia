-- Prove2me | Theorems.Thm_VarianceRegularization_Expansion_variance_sufficient
-- name    : VarianceRegularization.Expansion.variance_sufficient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:53:35.985964+00:00
-- url     : https://prove2.me/theorems/2e08ce48-d687-4c06-b4e2-7ded64cbaef9
-- title:
--   Appendix A, (30): a sufficient variance threshold
-- statement:
--   Let $n\ge1$, $\rho\ge0$, and suppose all sample values $z_i$ lie in $[M_0,M_1]$, where $M=M_1-M_0$. If the empirical variance is positive and
--
--   $$s_n^2\ge\frac{2\rho M^2}{n},$$
--
--   then the χ² robust expectation equals the empirical mean plus the standard-deviation penalty:
--
--   $$R_n(z,\rho)=\bar z+\sqrt{\frac{2\rho s_n^2}{n}}.$$
--
--   This threshold gives a sample-level certificate for the exact expansion.
--
--   **Formalization Note** The appendix has already restricted to positive sample variance before dividing by it in (30).
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 32, display (30)

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_robustSup
import Definitions.Def_VarianceRegularization_Expansion_empVar

namespace VarianceRegularization.Expansion

/-- Appendix A, p. 32, display (30): a variance threshold sufficient for the exact expansion.
The sample lies in `[M₀,M₁]`, hence every deviation from its mean is at most `M₁-M₀`. -/
theorem variance_sufficient {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁)
    (hvar : 0 < empVar z)
    (h30 : 2 * ρ * (M₁ - M₀) ^ 2 / (n : ℝ) ≤ empVar z) :
    robustSup n ρ z = empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z) := by sorry

end VarianceRegularization.Expansion
