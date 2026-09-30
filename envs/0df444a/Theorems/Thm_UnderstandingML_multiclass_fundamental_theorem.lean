-- Prove2me | Theorems.Thm_UnderstandingML_multiclass_fundamental_theorem
-- name    : UnderstandingML.multiclass_fundamental_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:58:25.649207+00:00
-- url     : https://prove2.me/theorems/e2600e97-87cf-425e-9c83-f4089a6b8ad5
-- title:
--   Theorem 29.3 (multiclass fundamental theorem): absolute constants bound the uniform-convergence, agnostic and realizable sample complexities of a class of Natarajan dimension d in terms of d, k, ε, δ
-- statement:
--   **Theorem 29.3 (The Multiclass Fundamental Theorem).** There exist absolute constants $C_1, C_2 > 0$ such that the following holds. For every hypothesis class $H$ of functions from $X$ to $[k]$, such that the Natarajan dimension of $H$ is $d$, we have
--   1. $H$ has the uniform convergence property with sample complexity $C_1\frac{d + \log(1/\delta)}{\epsilon^2} \le m^{UC}_H(\epsilon,\delta) \le C_2\frac{d\log(k) + \log(1/\delta)}{\epsilon^2}$.
--   2. $H$ is agnostic PAC learnable with sample complexity $C_1\frac{d + \log(1/\delta)}{\epsilon^2} \le m_H(\epsilon,\delta) \le C_2\frac{d\log(k) + \log(1/\delta)}{\epsilon^2}$.
--   3. $H$ is PAC learnable (assuming realizability) with sample complexity $C_1\frac{d + \log(1/\delta)}{\epsilon} \le m_H(\epsilon,\delta) \le C_2\frac{d\log(kd/\epsilon) + \log(1/\delta)}{\epsilon}$.
--
--   Formally, as Theorem 6.8 is stated in Mission IV: the upper bounds are achieved by every ERM learner for nonempty, measurable classes with the countable-approximation property, and the lower bounds hold for $\epsilon < \epsilon_0$, $\delta < \delta_0$, $d \ge 2$. The uniform-convergence upper bound is stated for $d \ge 1$: at $d = 0$ ($H$ a single function) it fails for every $C_2$, because $\log(1/\delta) \to 0$ as $\delta \to 1$ lets the bound reach $m = 1$, and a single example with a fair-coin label is never $\tfrac14$-representative. The agnostic and realizable upper bounds hold at $d = 0$ trivially.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.2 p. 403, Theorem 29.3

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace UnderstandingML

/-- **Theorem 29.3 (The Multiclass Fundamental Theorem)** (p. 403). There exist absolute
constants `C₁, C₂ > 0` such that for every hypothesis class `H` of functions from `X` to `[k]`
with Natarajan dimension `d`:
1. `H` has the uniform convergence property with sample complexity
   `C₁ (d + log(1/δ))/ε² ≤ m^{UC}_H(ε, δ) ≤ C₂ (d log(k) + log(1/δ))/ε²`;
2. `H` is agnostic PAC learnable with sample complexity
   `C₁ (d + log(1/δ))/ε² ≤ m_H(ε, δ) ≤ C₂ (d log(k) + log(1/δ))/ε²`;
3. `H` is PAC learnable (assuming realizability) with sample complexity
   `C₁ (d + log(1/δ))/ε ≤ m_H(ε, δ) ≤ C₂ (d log(kd/ε) + log(1/δ))/ε`.
As in Theorem 6.8 (Mission IV): the upper bounds hold for ERM learners of classes that are
nonempty, measurable and have the countable-approximation property; the lower bounds hold for
`ε < ε₀`, `δ < δ₀` and `d ≥ 2`. The uniform-convergence upper bound is stated for `d ≥ 1`: at
`d = 0` (`H` a single function) it is false for every `C₂`, since `log(1/δ) → 0` as `δ → 1` lets the
bound reach `m = 1`, and one example with a fair-coin label is never `1/4`-representative. -/
theorem multiclass_fundamental_theorem :
    ∃ C₁ C₂ ε₀ δ₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSingletonClass X]
        [MeasurableSpace Y] [MeasurableSingletonClass Y] [Fintype Y]
        (H : Set (X → Y)) (d : ℕ), H.Nonempty → (∀ h ∈ H, Measurable h) →
        NPointwiseSeparable H → ndim H = d →
        ((1 ≤ d → HasUniformConvergenceWith lossMulti H (fun ε δ ↦
            ⌈C₂ * (d * Real.log (Fintype.card Y) + Real.log (1 / δ)) / ε ^ 2⌉₊)) ∧
          ∀ mUC : ℝ → ℝ → ℕ, HasUniformConvergenceWith lossMulti H mUC →
            ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ → 2 ≤ d →
              C₁ * (d + Real.log (1 / δ)) / ε ^ 2 ≤ mUC ε δ) ∧
        ((∀ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A →
            IsAgnosticPACWith lossMulti H A (fun ε δ ↦
              ⌈C₂ * (d * Real.log (Fintype.card Y) + Real.log (1 / δ)) / ε ^ 2⌉₊)) ∧
          ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsAgnosticPACWith lossMulti H A mH →
            ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ → 2 ≤ d →
              C₁ * (d + Real.log (1 / δ)) / ε ^ 2 ≤ mH ε δ) ∧
        ((∀ A : Learner (X × Y) (X → Y), IsERMLearner lossMulti H A →
            IsMulticlassPACWith H A (fun ε δ ↦
              ⌈C₂ * (d * Real.log (Fintype.card Y * d / ε) + Real.log (1 / δ)) / ε⌉₊)) ∧
          ∀ (A : Learner (X × Y) (X → Y)) (mH : ℝ → ℝ → ℕ), IsMulticlassPACWith H A mH →
            ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ → 2 ≤ d →
              C₁ * (d + Real.log (1 / δ)) / ε ≤ mH ε δ) := by sorry

end UnderstandingML
