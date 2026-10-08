-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_expect_condSup_deviation
-- name    : RadGauss.Discrepancy.expect_condSup_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:33:31.19226+00:00
-- url     : https://prove2.me/theorems/c3408ff9-a3a2-4023-86be-9d066d12b797
-- title:
--   Appendix A — |E s(N) − s(EN)| ≤ E|s(N) − s(EN)| ≤ 4√(2/n)
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, $n = 2m$ with $m\ge1$, and $F$ a nonempty class of measurable functions $\mathcal X\to[-1,1]$. Let $N = \sum_{i=1}^n\sigma_i$ for independent uniform signs $\sigma_i$, so that $\mathbf EN = 0$. Then
--
--   $$
--   \bigl|\mathbf E\,s(N) - s(\mathbf EN)\bigr| \le \mathbf E\,\bigl|s(N) - s(\mathbf EN)\bigr| \le 4\sqrt{\frac{2}{n}}.
--   $$
--
--   Together with the two previous identities this bounds the gap between the Rademacher complexity and the expected maximum discrepancy.
--
--   **Formalization Note** Expectations over the signs are averages over all $2^n$ sign vectors, and $s(\mathbf EN)$ is written $s(0)$. The sample size is even so that $0$ is an attainable value of $N$. Added hypotheses as for the other statements.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 479 (PDF p. 17), Appendix A, last display

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479, last display: for `N = Σ_i σ_i` (so `E N = 0`) and `n = 2m`,
`|E s(N) − s(E N)| ≤ E|s(N) − s(E N)| ≤ 4 √(2/n)`. Expectations over uniform signs are averages
over all `2^n` sign vectors. -/
theorem expect_condSup_deviation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    |((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool, condSup μ (2 * m) F (sumSign σ)
        - condSup μ (2 * m) F 0|
      ≤ ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0| ∧
    ((2 : ℝ) ^ (2 * m))⁻¹ * ∑ σ : Fin (2 * m) → Bool,
          |condSup μ (2 * m) F (sumSign σ) - condSup μ (2 * m) F 0|
      ≤ 4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)) := by sorry

end RadGauss.Discrepancy
