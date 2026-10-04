-- Prove2me | Theorems.Thm_StabGen_Hypothesis_lemma9_empirical
-- name    : StabGen.Hypothesis.lemma9_empirical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:49:57.985368+00:00
-- url     : https://prove2.me/theorems/60b873c1-9827-42ba-b715-6b4fbc53b90f
-- title:
--   Lemma 9, eq. (8): $\mathbb E_S[(R - R_{\mathrm{emp}})^2] \le M^2/(2m) + 3M\,\mathbb E_{S,z_i'}|\ell(A_S,z_i) - \ell(A_{S^i},z_i)|$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Let $S = (z_1, \dots, z_m) \sim D^m$ with $m \ge 2$, let $z'_i \sim D$ be independent of $S$, and let $S^i$ be $S$ with $z_i$ replaced by $z'_i$. Then for every index $i$,
--
--   $$\mathbb E_S\bigl[(R(A,S) - R_{\mathrm{emp}}(A,S))^2\bigr] \le \frac{M^2}{2m} + 3M\,\mathbb E_{S,z'_i}\bigl[\,|\ell(A_S, z_i) - \ell(A_{S^i}, z_i)|\,\bigr].$$
--
--   The right-hand expectation measures how much the loss at a training point changes once that point is replaced by a fresh one. Together with Chebyshev's inequality this bound gives the empirical half of Theorem 11.
--
--   **Formalization Note** Lemma 9 is stated for $i, j$ with $i \ne j$, which presupposes $m \ge 2$; this is a hypothesis here. Inequality (8) involves only $i$. The expectation $\mathbb E_{S,z'_i}$ is the integral against $D^m \otimes D$, with $S^i$ = `replaceAt S i z'`.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 505, Lemma 9, eq. (8); proof in Appendix A, pp. 520–523

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem lemma9_empirical {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - EmpiricalError L S (A (trainingSet S))) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ M ^ 2 / (2 * (m : ℝ))
      + 3 * M * ∫ p : (Fin m → X × Y) × (X × Y),
          |Loss L (A (trainingSet p.1)) (p.1 i)
            - Loss L (A (trainingSet (replaceAt p.1 i p.2))) (p.1 i)|
        ∂((Measure.pi fun _ : Fin m => D).prod D) := by sorry

end StabGen.Hypothesis
