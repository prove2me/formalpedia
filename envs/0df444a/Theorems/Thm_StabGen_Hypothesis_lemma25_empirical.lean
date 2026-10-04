-- Prove2me | Theorems.Thm_StabGen_Hypothesis_lemma25_empirical
-- name    : StabGen.Hypothesis.lemma25_empirical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:49:03.298759+00:00
-- url     : https://prove2.me/theorems/e1e943b7-14e3-44f0-89dd-270e67d4d0e2
-- title:
--   Lemma 25 (empirical error): second-moment expansion of $R - R_{\mathrm{emp}}$
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let the cost satisfy $0 \le c(y', y) \le M$, and let $A$ be a symmetric deterministic learning algorithm whose losses are measurable. Let $S = (z_1, \dots, z_m) \sim D^m$ with $m \ge 2$, and let $z, z' \sim D$ be independent of each other and of $S$. Write $R = R(A,S)$ and $R_{\mathrm{emp}} = R_{\mathrm{emp}}(A,S)$. Then for any indices $i \ne j$,
--
--   $$\mathbb E_S\bigl[(R - R_{\mathrm{emp}})^2\bigr] \le \mathbb E_{S,z,z'}[\ell(A_S,z)\ell(A_S,z')] - 2\,\mathbb E_{S,z}[\ell(A_S,z)\ell(A_S,z_i)] + \mathbb E_S[\ell(A_S,z_i)\ell(A_S,z_j)] + \frac{M}{m}\mathbb E_S[\ell(A_S,z_i)] - \frac1m \mathbb E_S[\ell(A_S,z_i)\ell(A_S,z_j)] .$$
--
--   This is the generalized Rogers–Wagner lemma that opens the proof of Lemma 9: it expresses the second moment of the deviation through a few correlations of the loss.
--
--   **Formalization Note** The printed Lemma 25 has $\mathbb E_S[\ell(A_{S^{\setminus i}},z_i)\ell(A_{S^{\setminus j}},z_j)]$ as its third term, copied from the leave-one-out inequality. The paper's own proof (p. 521) bounds $\mathbb E_S[R_{\mathrm{emp}}^2]$ by $\frac{M}{m}\mathbb E_S[\ell(A_S,z_i)] + \frac{m-1}{m}\mathbb E_S[\ell(A_S,z_i)\ell(A_S,z_j)]$, and the rewriting as $I_1 + I_2 + I_3$ (pp. 521–522) uses $\ell(A_S,z_i)\ell(A_S,z_j)$; the statement here is that corrected form. The lemma is printed "for any learning algorithm", but its proof uses the standing assumptions of §2.1 (symmetry, measurability) and the bound $0 \le c \le M$; these are hypotheses here. $m \ge 2$ is implicit in the existence of $i \ne j$. Expectations over $(S,z)$ and $(S,z,z')$ are integrals against $D^m \otimes D$ and $(D^m \otimes D) \otimes D$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 520, Lemma 25 (first inequality; third term corrected per the proof on pp. 520–522)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting

open MeasureTheory

namespace StabGen.Hypothesis

open FoundationsML.Stability

theorem lemma25_empirical {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (M : ℝ)
    (hL : ∀ (y' : Y') (y : Y), 0 ≤ L y' y ∧ L y' y ≤ M)
    (A : LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable (fun p : (Fin n → X × Y) × (X × Y) =>
      Loss L (A (trainingSet p.1)) p.2))
    (m : ℕ) (hm : 2 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ∫ S : Fin m → X × Y,
        (GeneralizationError D L (A (trainingSet S)) - EmpiricalError L S (A (trainingSet S))) ^ 2
      ∂(Measure.pi fun _ : Fin m => D)
    ≤ ∫ p : ((Fin m → X × Y) × (X × Y)) × (X × Y),
          Loss L (A (trainingSet p.1.1)) p.1.2 * Loss L (A (trainingSet p.1.1)) p.2
        ∂(((Measure.pi fun _ : Fin m => D).prod D).prod D)
      - 2 * ∫ p : (Fin m → X × Y) × (X × Y),
          Loss L (A (trainingSet p.1)) p.2 * Loss L (A (trainingSet p.1)) (p.1 i)
        ∂((Measure.pi fun _ : Fin m => D).prod D)
      + ∫ S : Fin m → X × Y,
          Loss L (A (trainingSet S)) (S i) * Loss L (A (trainingSet S)) (S j)
        ∂(Measure.pi fun _ : Fin m => D)
      + M / (m : ℝ) * ∫ S : Fin m → X × Y, Loss L (A (trainingSet S)) (S i)
        ∂(Measure.pi fun _ : Fin m => D)
      - 1 / (m : ℝ) * ∫ S : Fin m → X × Y,
          Loss L (A (trainingSet S)) (S i) * Loss L (A (trainingSet S)) (S j)
        ∂(Measure.pi fun _ : Fin m => D) := by sorry

end StabGen.Hypothesis
