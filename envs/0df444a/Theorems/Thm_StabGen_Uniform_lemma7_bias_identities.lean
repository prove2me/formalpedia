-- Prove2me | Theorems.Thm_StabGen_Uniform_lemma7_bias_identities
-- name    : StabGen.Uniform.lemma7_bias_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:10:32.434405+00:00
-- url     : https://prove2.me/theorems/b33b0c70-2da6-4954-9e85-826b9afb3f8d
-- title:
--   Lemma 7 — bias identities for the empirical and leave-one-out errors
-- statement:
--   Let $D$ be a probability distribution on $Z = X \times Y$, let $S = (z_1, \dots, z_m) \sim D^m$, and let $z_i'$ and $z$ be further draws from $D$, independent of $S$. Let $A$ be a symmetric learning algorithm whose losses $\ell(A_T, z)$ are measurable and bounded. Write $R(A,S) = \mathbb E_z[\ell(A_S, z)]$, $R_{\mathrm{emp}}(A,S) = \frac1m\sum_j \ell(A_S, z_j)$ and $R_{\mathrm{loo}}(A,S) = \frac1m \sum_j \ell(A_{S^{\setminus j}}, z_j)$. Then for every $i \in \{1, \dots, m\}$:
--
--   1. $$\mathbb E_S[R(A,S) - R_{\mathrm{emp}}(A,S)] = \mathbb E_{S,z_i'}[\ell(A_S, z_i') - \ell(A_{S^i}, z_i')];$$
--   2. $$\mathbb E_S[R(A,S^{\setminus i}) - R_{\mathrm{loo}}(A,S)] = 0;$$
--   3. $$\mathbb E_S[R(A,S) - R_{\mathrm{loo}}(A,S)] = \mathbb E_{S,z}[\ell(A_S, z) - \ell(A_{S^{\setminus i}}, z)].$$
--
--   Here $S^i$ is $S$ with $z_i$ replaced by $z_i'$ and $S^{\setminus i}$ is $S$ with $z_i$ removed. The lemma expresses the bias of both estimators of the generalization error through the change of the loss when one training point is replaced or removed; with uniform stability it bounds the means $\mathbb E_S[R - R_{\mathrm{emp}}]$ and $\mathbb E_S[R - R_{\mathrm{loo}}]$ in Theorem 12.
--
--   **Formalization Note** Symmetry is built into the algorithm type (its input is a multiset). The paper's standing assumption that all functions are measurable is the hypothesis that $(S, z) \mapsto \ell(A_S, z)$ is jointly measurable at every sample size; boundedness, $|\ell(A_T, z)| \le M$ for some $M$ and every training set $T$, is added so that every expectation is a genuine integral and not Lean's default value $0$ for a non-integrable function (the paper applies the lemma to losses in $[0, M]$). The pair $(S, z_i')$ has law $D^m \otimes D$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 504–505, Lemma 7

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

/-- **Lemma 7** (Bousquet & Elisseeff 2002, pp. 504–505). For a symmetric learning algorithm and
every `i ∈ {1, …, m}`, with `S ∼ D^m` and `z'_i, z ∼ D` independent of `S`:
`E_S[R(A,S) − R_emp(A,S)] = E_{S,z'_i}[ℓ(A_S, z'_i) − ℓ(A_{S^i}, z'_i)]`,
`E_S[R(A,S^{\i}) − R_loo(A,S)] = 0`, and
`E_S[R(A,S) − R_loo(A,S)] = E_{S,z}[ℓ(A_S, z) − ℓ(A_{S^{\i}}, z)]`.
Measurability and boundedness of the losses make every expectation genuine. -/
theorem lemma7_bias_identities {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (hbdd : ∃ M : ℝ, ∀ (T : Multiset (X × Y)) (z : X × Y), |Loss L (A T) z| ≤ M)
    (m : ℕ) (i : Fin m) :
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        ∂(Measure.pi fun _ : Fin m => D)
      = ∫ p : (Fin m → X × Y) × (X × Y),
          (Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2 - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt p.1 i p.2))) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.removeAt S i)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D) = 0) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D)
      = ∫ p : (Fin m → X × Y) × (X × Y),
          (Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2 - Loss L (A (StabGen.Hypothesis.removeAt p.1 i)) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)) := by sorry

end StabGen.Uniform
