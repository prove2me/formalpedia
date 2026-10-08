-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_rademacher_le_discrepancy_union_neg
-- name    : RadGauss.Discrepancy.rademacher_le_discrepancy_union_neg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:33:21.683973+00:00
-- url     : https://prove2.me/theorems/23175e09-33e4-4e16-a3d9-c74e303f8fb1
-- title:
--   Appendix A — R_n(F) = R_n(F ∪ −F) ≤ D_n(F ∪ −F) + 4√(2/n)
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, $n = 2m$ with $m\ge1$, and $F$ a nonempty class of measurable functions $\mathcal X\to[-1,1]$. Write $-F = \{-f : f\in F\}$. Then
--
--   $$
--   R_n(F) = R_n(F\cup -F) \le D_n(F\cup -F) + 4\sqrt{\frac{2}{n}}.
--   $$
--
--   When $F$ is closed under negation, $F\cup-F = F$ and this is the strengthened lower bound of Lemma 3.
--
--   **Formalization Note** Since $R_n$ takes values in $[0,\infty]$, the real quantities $D_n(F\cup-F)$ (nonnegative here) and $4\sqrt{2/n}$ are embedded with `ENNReal.ofReal`. $-F$ is Mathlib's pointwise negation of a set, $\{g : -g\in F\} = \{-f : f\in F\}$. Added hypotheses as for the other statements; the measurability hypothesis on $F$ implies the one for $F\cup-F$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 480 (PDF p. 18), Appendix A, display

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 480: `R_n(F) = R_n(F ∪ −F) ≤ D_n(F ∪ −F) + 4 √(2/n)` for `n = 2m`. -/
theorem rademacher_le_discrepancy_union_neg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    RadGauss.RiskBound.rademacherComplexity μ (2 * m) F = RadGauss.RiskBound.rademacherComplexity μ (2 * m) (F ∪ -F) ∧
      RadGauss.RiskBound.rademacherComplexity μ (2 * m) (F ∪ -F)
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m (F ∪ -F))
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) := by sorry

end RadGauss.Discrepancy
