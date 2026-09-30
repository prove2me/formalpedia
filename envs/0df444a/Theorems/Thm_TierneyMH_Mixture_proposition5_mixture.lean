-- Prove2me | Theorems.Thm_TierneyMH_Mixture_proposition5_mixture
-- name    : TierneyMH.Mixture.proposition5_mixture
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T03:39:35.759798+00:00
-- url     : https://prove2.me/theorems/c2d370bf-6b4a-4534-b223-e78963393db5
-- title:
--   Proposition 5: the maximal kernel of a mixture proposal dominates the mixture of maximal kernels, $P\succeq\sum_i\beta_iP_i$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space with measurable singletons and a countably generated $\sigma$-algebra, and let $\pi$ be a probability measure on $E$ (the target). Let $(Q_i)_{i\in I}$ be a finite or countable family of Markov proposal kernels on $E$ and let $\beta_i\ge 0$ with $\sum_i\beta_i=1$. Let $P_i$ be the maximal Metropolis–Hastings kernel for $Q_i$, and let $P$ be the maximal Metropolis–Hastings kernel for the mixture proposal $Q=\sum_i\beta_iQ_i$. Then
--
--   $$P\;\succeq\;\sum_i\beta_iP_i,$$
--
--   that is, for $\pi$-almost every $x\in E$,
--
--   $$P(x,A\setminus\{x\})\;\ge\;\sum_i\beta_i\,P_i(x,A\setminus\{x\})\qquad\text{for all } A\in\mathcal E .$$
--
--   There are two ways of combining Metropolis–Hastings samplers built on proposals $Q_i$: mix the samplers, or run a single sampler with the mixture proposal. Combined with Peskun's theorem for general state spaces (Theorem 4 of the paper), the proposition shows that the second has asymptotic variances of sample-path averages no larger than the first, whatever the weights.
--
--   **Formalization Note** Two hypotheses implicit in the paper are made explicit: singletons are measurable, as the sets $A\setminus\{x\}$ and point masses $\delta_x$ require; and the $\sigma$-algebra $\mathcal E$ is countably generated. The second is an addition: the proof in the paper shows an inequality between measures on $E\times E$, and passing to the kernel-level statement, with one $\pi$-null set of exceptional $x$ for all $A$ simultaneously, uses a countable generating family. The weights are in `ℝ≥0` with `HasSum β 1`, and the index type is countable.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 7, Proposition 5

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Mixture_maxMHKernel
import Definitions.Def_TierneyMH_Mixture_mixKernel

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TierneyMH.Mixture

/-- **Proposition 5** (Tierney 1998, p. 7). Let `Qᵢ` be a (countable) sequence of Markov
proposal kernels and `βᵢ ≥ 0` with `∑ βᵢ = 1`. Let `Pᵢ` be the maximal Metropolis–Hastings
kernel for `Qᵢ` and `P` the maximal Metropolis–Hastings kernel for the mixture proposal
`Q = ∑ βᵢ Qᵢ`, all for the target `π`. Then `P ⪰ ∑ βᵢ Pᵢ`: for `π`-almost every `x`,
`P(x, A \ {x}) ≥ ∑ βᵢ Pᵢ(x, A \ {x})` for all measurable `A`.

Added hypotheses: measurable singletons (implicit in the paper's `A \ {x}`), and a countably
generated σ-algebra on `E`, which makes the exceptional `π`-null set uniform over `A`. -/
theorem proposition5_mixture {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [MeasurableSpace.CountablyGenerated E]
    (π : Measure E) [IsProbabilityMeasure π]
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)]
    (β : ι → ℝ≥0) (hβ : HasSum β 1) :
    OffDiagDominates π (maxMHKernel π (mixKernel β Q))
      (mixKernel β fun i => maxMHKernel π (Q i)) := by sorry

end TierneyMH.Mixture
