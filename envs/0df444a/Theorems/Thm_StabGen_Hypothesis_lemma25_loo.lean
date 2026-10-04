-- Prove2me | Theorems.Thm_StabGen_Hypothesis_lemma25_loo
-- name    : StabGen.Hypothesis.lemma25_loo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:49:31.303126+00:00
-- url     : https://prove2.me/theorems/1132eb3d-4ef7-4301-84a2-2a6267107966
-- title:
--   Lemma 25 (leave-one-out error): second-moment expansion of $R - R_{\mathrm{loo}}$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Let $S = (z_1, \dots, z_m) \sim D^m$ with $m \ge 2$, and let $z, z' \sim D$ be independent of each other and of $S$. Write $R = R(A,S)$, $R_{\mathrm{loo}} = R_{\mathrm{loo}}(A,S)$, and $R^{\setminus i} = R(A, S^{\setminus i}) = \mathbb E_z[\ell(A_{S^{\setminus i}}, z)]$. Then for any indices $i \ne j$,
--
--   $$\mathbb E_S\bigl[(R - R_{\mathrm{loo}})^2\bigr] \le \mathbb E_{S,z,z'}[\ell(A_S,z)\ell(A_S,z')] - 2\,\mathbb E_{S,z}[\ell(A_S,z)\ell(A_{S^{\setminus i}},z_i)] + \mathbb E_S[\ell(A_{S^{\setminus i}},z_i)\ell(A_{S^{\setminus j}},z_j)] + \frac{M}{m}\mathbb E_S\bigl[R^{\setminus i}\bigr] - \frac1m \mathbb E_S[\ell(A_{S^{\setminus i}},z_i)\ell(A_{S^{\setminus j}},z_j)] .$$
--
--   This is the leave-one-out half of the generalized Rogers–Wagner lemma used to prove Lemma 9.
--
--   **Formalization Note** As printed. The lemma is printed "for any learning algorithm", but its proof uses the standing assumptions of §2.1 (symmetry, measurability) and $0 \le c \le M$; these are hypotheses here, and $m \ge 2$ is implicit in $i \ne j$. Expectations over $(S,z)$ and $(S,z,z')$ are integrals against $D^m \otimes D$ and $(D^m \otimes D) \otimes D$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 520, Lemma 25 (second inequality)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem lemma25_loo {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - looError L A S) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ ∫ p : ((Fin m → X × Y) × (X × Y)) × (X × Y),
          Loss L (A (trainingSet p.1.1)) p.1.2 * Loss L (A (trainingSet p.1.1)) p.2
        ∂(((Measure.pi fun _ : Fin m => D).prod D).prod D)
      - 2 * ∫ p : (Fin m → X × Y) × (X × Y),
          Loss L (A (trainingSet p.1)) p.2 * Loss L (A (removeAt p.1 i)) (p.1 i)
        ∂((Measure.pi fun _ : Fin m => D).prod D)
      + ∫ S : Fin m → X × Y,
          Loss L (A (removeAt S i)) (S i) * Loss L (A (removeAt S j)) (S j)
        ∂(Measure.pi fun _ : Fin m => D)
      + M / (m : ℝ) * ∫ S : Fin m → X × Y, GeneralizationError D L (A (removeAt S i))
        ∂(Measure.pi fun _ : Fin m => D)
      - 1 / (m : ℝ) * ∫ S : Fin m → X × Y,
          Loss L (A (removeAt S i)) (S i) * Loss L (A (removeAt S j)) (S j)
        ∂(Measure.pi fun _ : Fin m => D) := by sorry

end StabGen.Hypothesis
