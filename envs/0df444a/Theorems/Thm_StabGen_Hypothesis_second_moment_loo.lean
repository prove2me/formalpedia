-- Prove2me | Theorems.Thm_StabGen_Hypothesis_second_moment_loo
-- name    : StabGen.Hypothesis.second_moment_loo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:09:24.978895+00:00
-- url     : https://prove2.me/theorems/a8f0d7d8-899f-4181-b4cf-a5206d690acc
-- title:
--   Proof of Theorem 11: $\mathbb E_S[(R - R_{\mathrm{loo}})^2] \le M^2/(2m) + 3M\beta_1$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Suppose that, at sample size $m \ge 2$, $A$ has hypothesis stability $\beta_1$. Then, with $S \sim D^m$,
--
--   $$\mathbb E_S\bigl[(R(A,S) - R_{\mathrm{loo}}(A,S))^2\bigr] \le \frac{M^2}{2m} + 3M\beta_1 .$$
--
--   Chebyshev's inequality applied to this second-moment bound gives the leave-one-out half of Theorem 11.
--
--   **Formalization Note** The bound is as printed. The paper says it follows "by (10)"; it follows from Lemma 9, eq. (9), together with Definition 3, whereas (10) would give a constant $6M\beta_1$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 506, proof of Theorem 11 ("Also, we have by (10)")

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Hypothesis_Stability

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem second_moment_loo {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (β₁ : ℝ) (h₁ : HypothesisStable D L A m β₁) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - looError L A S) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ)) + 3 * M * β₁ := by sorry

end StabGen.Hypothesis
