-- Prove2me | Theorems.Thm_StabGen_Hypothesis_replace_one_pointwise_bound
-- name    : StabGen.Hypothesis.replace_one_pointwise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:08:51.335061+00:00
-- url     : https://prove2.me/theorems/3aedbdac-92b0-4cc9-b140-eb3c3113bcbc
-- title:
--   Proof of Theorem 11: the replace-one term is at most $\beta_1 + \beta_2$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Suppose that, at sample size $m$, $A$ has hypothesis stability $\beta_1$ (Definition 3) and pointwise hypothesis stability $\beta_2$ (Definition 4). Let $S = (z_1, \dots, z_m) \sim D^m$, let $z'_i \sim D$ be independent of $S$, and let $S^i$ be $S$ with $z_i$ replaced by $z'_i$. Then for every index $i$,
--
--   $$\mathbb E_{S,z'_i}\bigl[\,|\ell(A_S, z_i) - \ell(A_{S^i}, z_i)|\,\bigr] \le \beta_1 + \beta_2 .$$
--
--   This converts the replace-one quantity in Lemma 9, eq. (8), into the two remove-one stability notions of the paper.
--
--   **Formalization Note** The paper prints the bound $2\beta_2$. Its argument splits the quantity, by the triangle inequality, into $\mathbb E_S[|\ell(A_S,z_i) - \ell(A_{S^{\setminus i}},z_i)|] \le \beta_2$ and $\mathbb E_{S,z'_i}[|\ell(A_{S^{\setminus i}},z_i) - \ell(A_{S^i},z_i)|]$. In the second term $z_i$ is not in $S^i$ and $(S^i)^{\setminus i} = S^{\setminus i}$, so it is an instance of Definition 3 and is bounded by $\beta_1$, not $\beta_2$. The statement here is the bound the argument proves; it agrees with the printed one when $\beta_1 = \beta_2$. Expectation over $(S, z'_i)$ is the integral against $D^m \otimes D$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 506, proof of Theorem 11 (first display; printed bound 2β2 corrected to β1 + β2)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Hypothesis_Stability

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem replace_one_pointwise_bound {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (β₁ β₂ : ℝ) (h₁ : HypothesisStable D L A m β₁)
    (h₂ : PointwiseHypothesisStable D L A m β₂) (i : Fin m) :
    ∫ p : (Fin m → X × Y) × (X × Y),
        |Loss L (A (trainingSet p.1)) (p.1 i)
          - Loss L (A (trainingSet (replaceAt p.1 i p.2))) (p.1 i)|
      ∂((Measure.pi fun _ : Fin m => D).prod D)
    ≤ β₁ + β₂ := by sorry

end StabGen.Hypothesis
