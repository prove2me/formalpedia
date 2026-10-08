-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_4_1
-- name    : PoissonDepTrials.MixSqrt.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:01.381022+00:00
-- url     : https://prove2.me/theorems/d031b9ad-f2b1-45a5-92bc-099d197260d5
-- title:
--   Lemma 4.1, pp. 538–539 — a uniform conditional bound (4.2) gives a regular conditional law within α of the law of Z (4.3)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y$ a random element of a measurable space $(R,\mathcal A)$ and $Z$ a random element of a standard Borel space $(S,\mathcal B)$. Suppose that for some $\alpha$ and every $B\in\mathcal B$,
--   $$\bigl|P(Z\in B\mid Y)-P(Z\in B)\bigr|\le\alpha\quad\text{almost surely}.\tag{4.2}$$
--   Then there exist a regular conditional distribution $\hat P_y$ of $Z$ given $Y=y$ — a Markov kernel from $R$ to $S$ such that the law of $Y$ composed with $\hat P$ is the joint law of $(Y,Z)$ — and a set $M\in\mathcal A$ with $P(Y\in M)=1$ such that for every $y\in M$
--   $$\sup_{B\in\mathcal B}\bigl|\hat P_y(B)-\hat P(B)\bigr|\le\alpha,\tag{4.3}$$
--   where $\hat P$ is the distribution of $Z$.
--
--   The lemma upgrades a family of almost-sure bounds, one per event, into a single null set outside which the bound holds for all events simultaneously; Lemma 4.2 integrates it against a bounded function.
--
--   **Formalization Note** "Borel space" is Mathlib's `StandardBorelSpace`; `Nonempty S` is added so the kernel API applies (it follows from the existence of $Z$). The regular conditional probability is a Markov kernel $\kappa$ with $\mathrm{law}(Y)\otimes\kappa=\mathrm{law}(Y,Z)$. $P(Z\in B\mid Y)$ is the conditional expectation of the indicator given $\sigma(Y)$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 538–539, Lemma 4.1, (4.2), (4.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.1, pp. 538–539. If `|P(Z ∈ B | Y) − P(Z ∈ B)| ≤ α` almost surely for every
measurable `B` (4.2), and `S` is a standard Borel space, then there is a regular conditional
distribution `κ` of `Z` given `Y` (a Markov kernel with `law(Y) ⊗ κ = law(Y, Z)`) and a measurable
set `M` with `P(Y ∈ M) = 1` such that `|κ_y(B) − P(Z ∈ B)| ≤ α` for all `y ∈ M` and all measurable
`B` (4.3). -/
theorem lemma_4_1 {Ω R S : Type*} [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace S]
    [StandardBorelSpace S] [Nonempty S] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → R) (Z : Ω → S) (hY : Measurable Y) (hZ : Measurable Z) (α : ℝ)
    (h42 : ∀ B : Set S, MeasurableSet B →
      ∀ᵐ ω ∂P, |(P[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Y inferInstance]) ω - P.real (Z ⁻¹' B)| ≤ α) :
    ∃ κ : Kernel R S, IsMarkovKernel κ ∧ (P.map Y) ⊗ₘ κ = P.map (fun ω => (Y ω, Z ω)) ∧
      ∃ M : Set R, MeasurableSet M ∧ P (Y ⁻¹' M) = 1 ∧
        ∀ y ∈ M, ∀ B : Set S, MeasurableSet B → |(κ y B).toReal - (P.map Z).real B| ≤ α := by sorry

end PoissonDepTrials.MixSqrt
