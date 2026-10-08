-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_1
-- name    : PoissonDepTrials.MixInv.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:55:17.005001+00:00
-- url     : https://prove2.me/theorems/c9ed5cdf-58e1-4fd1-a1f1-6797e5f8d591
-- title:
--   Lemma 4.1, p. 538 — under (4.2) there is a regular conditional probability within α of the law of Z, uniformly in B
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $Y$, $Z$ random elements with values in measurable spaces $(R,\mathcal A)$ and $(S,\mathcal B)$, where $(S,\mathcal B)$ is a Borel space. Suppose that for every $B\in\mathcal B$,
--   $$|P(Z\in B\mid Y)-P(Z\in B)|\le\alpha\quad\text{a.s.}\tag{4.2}$$
--   Then there is a regular conditional probability $\hat P_y$ for $Z$ given $Y=y$ and a set $M\in\mathcal A$ with $P(Y\in M)=1$ such that for every $y\in M$,
--   $$\sup_{B\in\mathcal B}|\hat P_y(B)-\hat P(B)|\le\alpha,$$
--   where $\hat P$ is the distribution of $Z$. It is the measure-theoretic step behind the conditional covariance bound of Lemma 4.2.
--
--   **Formalization Note** "Borel space" is `StandardBorelSpace S` (with `Nonempty S`, automatic since $Z$ takes values in $S$). A regular conditional probability is a Markov kernel $\kappa$ with $P_Y\otimes\kappa=P_{(Y,Z)}$, and the supremum bound is stated for every measurable $B$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 538–539, Lemma 4.1, (4.2), (4.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_1 {Ω R S : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace S]
    [StandardBorelSpace S] [Nonempty S] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → R) (Z : Ω → S) (hY : Measurable Y) (hZ : Measurable Z) (α : ℝ)
    (h42 : ∀ B : Set S, MeasurableSet B → ∀ᵐ ω ∂P,
      |(P[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Y inferInstance]) ω
        - P.real (Z ⁻¹' B)| ≤ α) :
    ∃ κ : ProbabilityTheory.Kernel R S, IsMarkovKernel κ ∧
      (P.map Y) ⊗ₘ κ = P.map (fun ω => (Y ω, Z ω)) ∧
      ∃ M : Set R, MeasurableSet M ∧ P (Y ⁻¹' M) = 1 ∧
        ∀ y ∈ M, ∀ B : Set S, MeasurableSet B → |(κ y B).toReal - (P.map Z).real B| ≤ α := by sorry

end PoissonDepTrials.MixInv
