-- Prove2me | Theorems.Thm_StabGen_Hypothesis_hypothesis_stability_generalization_bound
-- name    : StabGen.Hypothesis.hypothesis_stability_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:09:30.845069+00:00
-- url     : https://prove2.me/theorems/8bc1e765-f1be-43ea-bbbe-7d8bd898cf48
-- title:
--   Theorem 11: polynomial generalization bounds from hypothesis stability
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$ and let the cost function satisfy $0 \le c(y', y) \le M$. Let $A$ be a symmetric deterministic learning algorithm whose losses are measurable, and suppose that at sample size $m \ge 1$ it has hypothesis stability $\beta_1$ (Definition 3) and pointwise hypothesis stability $\beta_2$ (Definition 4). Draw the training set $S \sim D^m$. Then for every $\delta > 0$, with probability at least $1 - \delta$,
--
--   $$R(A,S) \le R_{\mathrm{emp}}(A,S) + \sqrt{\frac{M^2 + 6Mm(\beta_1 + \beta_2)}{2m\delta}},$$
--
--   and, with probability at least $1 - \delta$,
--
--   $$R(A,S) \le R_{\mathrm{loo}}(A,S) + \sqrt{\frac{M^2 + 6Mm\beta_1}{2m\delta}}.$$
--
--   Here $R$ is the generalization error, $R_{\mathrm{emp}}$ the empirical error and $R_{\mathrm{loo}}$ the leave-one-out error of $A_S$. The theorem shows that the two classical estimators of the risk deviate from it by $O(1/\sqrt{m\delta})$ whenever the algorithm's stability decays like $1/m$, without any capacity measure of the hypothesis space.
--
--   **Formalization Note** The two bounds are stated separately: the probability, under $D^m$, of the failure event $\{R > R_{\mathrm{emp}} + \cdots\}$ is at most $\delta$, and likewise for $R_{\mathrm{loo}}$. The paper prints the empirical bound with $12Mm\beta_2$ in place of $6Mm(\beta_1+\beta_2)$. Its proof bounds the replace-one term of Lemma 9, eq. (8), by $2\beta_2$, but one of the two summands is a hypothesis-stability term bounded by $\beta_1$; the bound the proof establishes is the one stated here, which coincides with the printed one when $\beta_1 = \beta_2$. The leave-one-out bound is as printed. The sample size is $m \ge 1$ (a training set has at least one point; at $m = 0$ the stability hypotheses are vacuous and the statement fails). The paper's proof goes through Lemmas 9 and 25, which need two distinct indices; at $m = 1$ the bounds still hold, by comparing $A_S$ with $A_\emptyset$ directly, so no restriction $m \ge 2$ is imposed.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 506, Theorem 11 (empirical constant 12Mmβ2 corrected to 6Mm(β1 + β2), per the proof on p. 506)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Hypothesis_Stability

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem hypothesis_stability_generalization_bound {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 1 ≤ m) (β₁ β₂ : ℝ) (h₁ : HypothesisStable D L A m β₁)
    (h₂ : PointwiseHypothesisStable D L A m β₂) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin m => D)
        {S | EmpiricalError L S (A (trainingSet S))
              + Real.sqrt ((M ^ 2 + 6 * M * (m : ℝ) * (β₁ + β₂)) / (2 * (m : ℝ) * δ))
            < GeneralizationError D L (A (trainingSet S))} ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin m => D)
        {S | looError L A S
              + Real.sqrt ((M ^ 2 + 6 * M * (m : ℝ) * β₁) / (2 * (m : ℝ) * δ))
            < GeneralizationError D L (A (trainingSet S))} ≤ ENNReal.ofReal δ := by sorry

end StabGen.Hypothesis
