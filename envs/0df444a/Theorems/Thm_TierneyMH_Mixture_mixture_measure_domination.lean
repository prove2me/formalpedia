-- Prove2me | Theorems.Thm_TierneyMH_Mixture_mixture_measure_domination
-- name    : TierneyMH.Mixture.mixture_measure_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T03:14:49.956353+00:00
-- url     : https://prove2.me/theorems/651f49a1-b95c-4123-a3c1-1792f10830dd
-- title:
--   Measure-level domination: $\pi(dx)Q(x,dy)\alpha_{MH}(x,y)\ge\sum_i\beta_i\pi(dx)Q_i(x,dy)\alpha^{(i)}_{MH}(x,y)$
-- statement:
--   Let $\pi$ be a probability measure on $E$, let $(Q_i)_{i\in I}$ be a finite or countable family of Markov proposal kernels, and let $\beta_i\ge0$ with $\sum_i\beta_i=1$. Let $Q=\sum_i\beta_iQ_i$ be the mixture proposal, let $\alpha_{MH}$ be the maximal acceptance probability for $Q$ and $\alpha^{(i)}_{MH}$ the one for $Q_i$ (all for the target $\pi$). Then, as measures on $E\times E$,
--
--   $$\pi(dx)\,Q(x,dy)\,\alpha_{MH}(x,y)\;\ge\;\sum_i\beta_i\,\pi(dx)\,Q_i(x,dy)\,\alpha^{(i)}_{MH}(x,y),$$
--
--   that is, the inequality holds when both sides are evaluated on any measurable set $S\subseteq E\times E$.
--
--   This is the whole computation of the proof of Proposition 5. It compares the accepted parts of one step of the two samplers: the Metropolis–Hastings sampler with the mixture proposal accepts at least as much mass, set by set in the joint law of current and next state, as the mixture of the component samplers.
--
--   **Formalization Note** Weights are in `ℝ≥0` with `HasSum β 1`; the index type is countable. No hypothesis on the σ-algebra of $E$ is needed at this measure level.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 8, proof of Proposition 5 (the whole display)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_alphaMH
import Definitions.Def_TierneyMH_Mixture_mixKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TierneyMH.Mixture

/-- **Measure-level domination** (Tierney 1998, proof of Proposition 5, p. 8, the whole
display). Let `Qᵢ` be a countable family of Markov proposal kernels and `βᵢ ≥ 0` weights with
`∑ βᵢ = 1`, `Q = ∑ βᵢ Qᵢ`, and let `α_MH`, `α_MH^{(i)}` be the maximal acceptance probabilities
for `Q`, `Qᵢ` and the target `π`. Then, as measures on `E × E`,
`π(dx) Q(x, dy) α_MH(x, y) ≥ ∑ βᵢ π(dx) Qᵢ(x, dy) α_MH^{(i)}(x, y)`,
i.e. the inequality holds on every measurable `S ⊆ E × E`. -/
theorem mixture_measure_domination {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)]
    (β : ι → ℝ≥0) (hβ : HasSum β 1) (S : Set (E × E)) (hS : MeasurableSet S) :
    ∑' i, (β i : ℝ≥0∞) * ((π ⊗ₘ Q i).withDensity (alphaMH π (Q i))) S ≤
      ((π ⊗ₘ mixKernel β Q).withDensity (alphaMH π (mixKernel β Q))) S := by sorry

end TierneyMH.Mixture
