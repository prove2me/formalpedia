-- Prove2me | Theorems.Thm_StabGen_Hypothesis_second_moment_empirical
-- name    : StabGen.Hypothesis.second_moment_empirical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:09:05.82429+00:00
-- url     : https://prove2.me/theorems/1684943c-557e-4996-a71c-8ce61890ed7e
-- title:
--   Proof of Theorem 11: $\mathbb E_S[(R - R_{\mathrm{emp}})^2] \le M^2/(2m) + 3M(\beta_1+\beta_2)$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Suppose that, at sample size $m \ge 2$, $A$ has hypothesis stability $\beta_1$ and pointwise hypothesis stability $\beta_2$. Then, with $S \sim D^m$,
--
--   $$\mathbb E_S\bigl[(R(A,S) - R_{\mathrm{emp}}(A,S))^2\bigr] \le \frac{M^2}{2m} + 3M(\beta_1 + \beta_2).$$
--
--   Chebyshev's inequality applied to this second-moment bound gives the empirical half of Theorem 11.
--
--   **Formalization Note** The paper prints $\frac{M^2}{2m} + 6M\beta_2$, which follows from Lemma 9, eq. (8), and the printed bound $2\beta_2$ on the replace-one term. That bound is in fact $\beta_1 + \beta_2$ (see the preceding milestone), so the proven inequality is the one stated here; the two agree when $\beta_1 = \beta_2$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 506, proof of Theorem 11 ("We thus get by (8)"; printed 6Mβ2 corrected to 3M(β1 + β2))

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Hypothesis_Stability

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem second_moment_empirical {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (β₁ β₂ : ℝ) (h₁ : HypothesisStable D L A m β₁)
    (h₂ : PointwiseHypothesisStable D L A m β₂) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - EmpiricalError L S (A (trainingSet S))) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ)) + 3 * M * (β₁ + β₂) := by sorry

end StabGen.Hypothesis
