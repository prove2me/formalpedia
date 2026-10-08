-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_rademacher_ge_expect_condSup
-- name    : RadGauss.Discrepancy.rademacher_ge_expect_condSup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:32:57.309006+00:00
-- url     : https://prove2.me/theorems/5ed64285-5dc9-4089-84f0-743d41267b5b
-- title:
--   Appendix A — R_n(F) ≥ E s(Σσ_i), with equality when F = −F
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, $n \ge 1$, and $F$ a nonempty class of measurable functions $\mathcal X \to [-1,1]$. Let $s$ be the conditional supremum function of Appendix A and $\sigma_1,\dots,\sigma_n$ independent uniform signs. Then
--
--   $$
--   R_n(F) = \mathbf E\sup_{f\in F}\left|\frac2n\sum_{i=1}^n\sigma_i f(X_i)\right| \;\ge\; \mathbf E\sup_{f\in F}\frac2n\sum_{i=1}^n\sigma_i f(X_i) \;=\; \mathbf E\, s\!\left(\sum_{i=1}^n\sigma_i\right),
--   $$
--
--   and the inequality is an equality when $f\in F$ implies $-f\in F$.
--
--   This connects the Rademacher complexity with the function $s$, whose value at $0$ is the expected maximum discrepancy.
--
--   **Formalization Note** $\mathbf E\,s(\sum_i\sigma_i)$ is the average of $s(\sum_i\sigma_i)$ over all $2^n$ sign vectors, embedded in $[0,\infty]$ with `ENNReal.ofReal` (its value is nonnegative under the hypotheses). Added hypotheses, which the paper uses implicitly: $F$ nonempty, every $f\in F$ measurable, and for every sign vector $\sigma$ the map $x \mapsto \sup_{f\in F}\sum_i\sigma_i f(x_i)$ is measurable, so that the expectations are genuine.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 479 (PDF p. 17), Appendix A, first display

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479, first display: `R_n(F) ≥ E s(Σ_i σ_i)`, with equality when `F` is closed
under negation. The expectation over uniform signs is the average over all `2^n` sign vectors. -/
theorem rademacher_ge_expect_condSup {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin n → Bool,
      Measurable fun x : Fin n → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))
        ≤ RadGauss.RiskBound.rademacherComplexity μ n F ∧
      ((∀ f ∈ F, -f ∈ F) →
        RadGauss.RiskBound.rademacherComplexity μ n F =
          ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, condSup μ n F (sumSign σ))) := by sorry

end RadGauss.Discrepancy
