-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_lemma_3
-- name    : RadGauss.Discrepancy.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:33:37.397821+00:00
-- url     : https://prove2.me/theorems/4f2c3ef6-bae3-4d15-952a-6821a6fe18cb
-- title:
--   Lemma 3 — R_n(F)/2 − 2√(2/n) ≤ D_n(F) ≤ R_n(F) + 4√(2/n), and R_n(F) − 4√(2/n) ≤ D_n(F) if F = −F
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal X$, let $n = 2m$ with $m\ge1$, and let $F$ be a nonempty class of measurable functions mapping $\mathcal X$ to $[-1,1]$. Let $R_n(F)$ be the Rademacher complexity and $D_n(F)$ the expected maximum discrepancy of $F$ (Definition 2). Then
--
--   $$
--   \frac{R_n(F)}{2} - 2\sqrt{\frac2n} \;\le\; D_n(F) \;\le\; R_n(F) + 4\sqrt{\frac2n}.
--   $$
--
--   If $F$ is closed under negation ($f\in F$ implies $-f\in F$), the lower bound can be strengthened to
--
--   $$
--   R_n(F) - 4\sqrt{\frac2n} \le D_n(F).
--   $$
--
--   So the expected maximum discrepancy and the Rademacher complexity are equivalent up to a factor $2$ and an additive $O(1/\sqrt n)$, and either may replace the other in data-dependent risk bounds.
--
--   **Formalization Note**
--   1. The sample size is even, $n = 2m$, $m \ge 1$, because $\hat D_n$ is defined with half sums; for odd $n$ the paper's $n/2$ is undefined.
--   2. Since $R_n$ takes values in $[0,\infty]$, each inequality $a - c \le D$ is written $a \le D + c$, with the real quantities $D_n(F)$ and $c$ embedded by `ENNReal.ofReal`; for $D_n(F) \ge 0$ (true for nonempty $F$) and finite $R_n(F)$ (true for $F$ bounded) this is equivalent to the printed form.
--   3. Added hypotheses, which the paper uses implicitly: $F$ nonempty, every $f\in F$ measurable, and for every sign vector $\sigma$ the map $x\mapsto\sup_{f\in F}\sum_i\sigma_i f(x_i)$ is measurable, so that $D_n$ is a genuine expectation.
--   4. The third display of Lemma 3, $P\{|\hat D_n(F)-D_n(F)|\ge\epsilon\}\le 2\exp(-\epsilon^2 n/2)$, is not part of this statement: it is false as printed (for $F=\{f\}$, $f(X)$ uniform on $\{\pm1\}$, $n=2$, $\epsilon=2$, the left side is $1/2 > 2e^{-4}$).
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 465 (PDF p. 3), Lemma 3, first and second displays

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- **Lemma 3** (p. 465), first and second displays, for `n = 2m`:
`R_n(F)/2 − 2√(2/n) ≤ D_n(F) ≤ R_n(F) + 4√(2/n)`, and `R_n(F) − 4√(2/n) ≤ D_n(F)` when `F` is
closed under negation. Subtractions are moved to the other side to avoid truncated subtraction
in `ℝ≥0∞`. -/
theorem lemma_3 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i)) :
    (RadGauss.RiskBound.rademacherComplexity μ (2 * m) F / 2
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (2 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ))) ∧
      ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
        ≤ RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) ∧
    ((∀ f ∈ F, -f ∈ F) →
      RadGauss.RiskBound.rademacherComplexity μ (2 * m) F
        ≤ ENNReal.ofReal (expectedMaxDiscrepancy μ m F)
          + ENNReal.ofReal (4 * Real.sqrt (2 / ((2 * m : ℕ) : ℝ)))) := by sorry

end RadGauss.Discrepancy
