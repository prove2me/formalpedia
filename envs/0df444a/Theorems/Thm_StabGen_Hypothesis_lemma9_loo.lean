-- Prove2me | Theorems.Thm_StabGen_Hypothesis_lemma9_loo
-- name    : StabGen.Hypothesis.lemma9_loo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:50:10.86128+00:00
-- url     : https://prove2.me/theorems/f37e5f65-5e04-4528-83d6-dcfe43544780
-- title:
--   Lemma 9, eq. (9): $\mathbb E_S[(R - R_{\mathrm{loo}})^2] \le M^2/(2m) + 3M\,\mathbb E_{S,z}|\ell(A_S,z) - \ell(A_{S^{\setminus i}},z)|$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Let $S = (z_1, \dots, z_m) \sim D^m$ with $m \ge 2$ and let $z \sim D$ be independent of $S$. Then for every index $i$,
--
--   $$\mathbb E_S\bigl[(R(A,S) - R_{\mathrm{loo}}(A,S))^2\bigr] \le \frac{M^2}{2m} + 3M\,\mathbb E_{S,z}\bigl[\,|\ell(A_S, z) - \ell(A_{S^{\setminus i}}, z)|\,\bigr].$$
--
--   The expectation on the right is exactly the quantity that hypothesis stability (Definition 3) bounds, so this inequality turns hypothesis stability into a second-moment bound for the leave-one-out estimator.
--
--   **Formalization Note** Lemma 9 is stated for $i, j$ with $i \ne j$, which presupposes $m \ge 2$; this is a hypothesis here. The expectation $\mathbb E_{S,z}$ is the integral against $D^m \otimes D$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 505, Lemma 9, eq. (9); proof in Appendix A, pp. 520–523

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem lemma9_loo {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - looError L A S) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ))
      + 3 * M * ∫ p : (Fin m → X × Y) × (X × Y),
          |Loss L (A (trainingSet p.1)) p.2 - Loss L (A (removeAt p.1 i)) p.2|
        ∂((Measure.pi fun _ : Fin m => D).prod D) := by sorry

end StabGen.Hypothesis
