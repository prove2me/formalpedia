-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_discrepancy_eq_condSup_zero
-- name    : RadGauss.Discrepancy.discrepancy_eq_condSup_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:33:08.791001+00:00
-- url     : https://prove2.me/theorems/dbc719ed-ee2c-4431-9f2d-5cfa492e4141
-- title:
--   Appendix A — D_n(F) = s(0) = s(E Σσ_i)
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, let $n = 2m$ with $m \ge 1$, and let $F$ be a nonempty class of measurable functions $\mathcal X \to [-1,1]$. Then the expected maximum discrepancy equals the conditional supremum function at zero:
--
--   $$
--   D_n(F) = s(0) = s\!\left(\mathbf E\sum_{i=1}^n\sigma_i\right).
--   $$
--
--   The identity expresses the fact that, because $X_1,\dots,X_n$ are i.i.d., every balanced split of the sample into two halves is equivalent to the fixed split used in the definition of $\hat D_n$.
--
--   **Formalization Note** Stated as $D_n(F) = s(0)$; $\mathbf E\sum_i\sigma_i = 0$. The sample size is even ($n = 2m$) because $\hat D_n$ needs half sums. Added hypotheses as for the other statements: $F$ nonempty, members measurable, and measurability of $x\mapsto\sup_{f\in F}\sum_i\sigma_i f(x_i)$ for every sign vector.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 479 (PDF p. 17), Appendix A, display after the first display

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479: `D_n(F) = s(0) = s(E Σ_i σ_i)` for `n = 2m`. -/
theorem discrepancy_eq_condSup_zero {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    expectedMaxDiscrepancy μ m F = condSup μ (2 * m) F 0 := by sorry

end RadGauss.Discrepancy
