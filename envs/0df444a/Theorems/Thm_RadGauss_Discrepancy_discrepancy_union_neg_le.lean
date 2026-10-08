-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_discrepancy_union_neg_le
-- name    : RadGauss.Discrepancy.discrepancy_union_neg_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:33:31.419888+00:00
-- url     : https://prove2.me/theorems/4822d05b-2dbb-4e80-8ee7-1df8e99fe36c
-- title:
--   Appendix A — D_n(F ∪ −F) ≤ 2D_n(F) + D_n({f₀, −f₀}) (corrected form of D_n(F ∪ −F) ≤ 2D_n(F))
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, $n = 2m$ with $m\ge1$, and $F$ a nonempty class of measurable functions $\mathcal X\to[-1,1]$. Then for every $f_0\in F$,
--
--   $$
--   D_n(F\cup -F) \le 2D_n(F) + D_n(\{f_0,-f_0\}),
--   $$
--
--   where $D_n(\{f_0,-f_0\}) = \mathbf E\left|\frac2n\sum_{i=1}^{n/2}f_0(X_i) - \frac2n\sum_{i=n/2+1}^n f_0(X_i)\right| \le \frac{2}{\sqrt n}$.
--
--   This is the step that passes from a class closed under negation to a general class in the lower bound of Lemma 3.
--
--   **Formalization Note** The paper states $D_n(F\cup-F)\le 2D_n(F)$. With the maximum discrepancy as defined on p. 464 (no absolute value) that inequality is false: for $F=\{f\}$ with $f(X)$ uniform on $\{\pm1\}$ and $n=2$, $D_2(F\cup-F) = \mathbf E|f(X_1)-f(X_2)| = 1$ while $D_2(F) = \mathbf E(f(X_1)-f(X_2)) = 0$. The statement here adds the correction term $D_n(\{f_0,-f_0\})$ for an arbitrary $f_0\in F$, which is what the argument (each half of $F \cup -F$ has the law of $F$, and the two suprema can be negative at most by $|\cdot|$ of a single member) gives. Added hypotheses as for the other statements.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 480 (PDF p. 18), Appendix A, sentence 'In general, it is easy to see that D_n(F ∪ −F) ≤ 2D_n(F)' (corrected)

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 480, `D_n(F ∪ −F) ≤ 2 D_n(F)`, **corrected**: with the page's signed `D̂_n` the
printed inequality fails for a singleton class, and the correct bound carries the extra term
`D_n({f₀, −f₀}) = E |(2/n) Σ_{i ≤ n/2} f₀(X_i) − (2/n) Σ_{i > n/2} f₀(X_i)|` for any `f₀ ∈ F`. -/
theorem discrepancy_union_neg_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin (2 * m) → Bool,
      Measurable fun x : Fin (2 * m) → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i))
    (f₀ : X → ℝ) (hf₀ : f₀ ∈ F) :
    expectedMaxDiscrepancy μ m (F ∪ -F)
      ≤ 2 * expectedMaxDiscrepancy μ m F
        + expectedMaxDiscrepancy μ m ({f₀, -f₀} : Set (X → ℝ)) := by sorry

end RadGauss.Discrepancy
