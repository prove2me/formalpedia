-- Prove2me | Theorems.Thm_SatisficingTS_sum_condMutualInfo_le_mutualInfo
-- name    : SatisficingTS.sum_condMutualInfo_le_mutualInfo
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:27.550626+00:00
-- url     : https://prove2.me/theorems/59fa2671-6ba1-4ae9-89f6-4de8a45bef61
-- title:
--   Proof of Theorem 1, p.8 — $\sum_{t=0}^T I(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1})\le I(\tilde A;\theta)$ for every $T$ (corrected: benchmark randomness independent of the policy's)
-- statement:
--   Work in the model of §2 with a policy $\psi$, and let $\tilde A=f(\theta,\zeta)$ be a benchmark action whose randomness $\zeta$ is independent of $(\theta,(W_t)_{t\ge0},\xi)$. Then for every $T\ge0$
--   $$
--   \sum_{t=0}^{T} I\bigl(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1}\bigr)\le I(\tilde A;\theta).
--   $$
--
--   The information about the benchmark accumulated over the first $T+1$ periods is bounded by the information $\theta$ carries about it. The paper obtains it from the chain rule $\sum_{t\le T}I(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1})=I(\tilde A;\mathcal H_T)$ and the data-processing bound $I(\tilde A;\mathcal H_T)\le I(\tilde A;\theta)$.
--
--   Differences from the source:
--   - correction: Ã = f(θ, ξ) with ξ independent of the disturbances, ξ being the paper's notation for the policy's exogenous randomness (§2, p.5) → Ã = f(θ, ζ) with the benchmark's randomness ζ independent of (θ, (W_t)_t, ξ) (IsBenchmark); reason: with the policy's ξ shared the theorem is false: θ constant, actions [0,1] ∪ {z₀, z₁} with µ = 1 on [0,1] and µ(z₀) = µ(z₁) = 0, noiseless Y_t = µ(A_t), ξ ~ Unif[0,1], D = 0, Ã = ξ, and the policy plays z_{b_t(ξ)} (b_t the t-th binary digit of ξ); then I(Ã;θ) = 0, I_t = log 2, E[R̃ − R_t] = 1, Γ = 1/log 2, so the bound is 0 while SRegret = 1/(1−α)
--   - encoding: H_{t−1} = (A_0, Y_0, …, A_{t−1}, Y_{t−1}), H_T → hist ψ g θ W ξ t (t entries), H_T = hist … (T+1); reason: 0-based indexing of the same tuple; no instance changes
--   - encoding: action set A and outcome set Y arbitrary → standard Borel, nonempty measurable spaces; reason: the conditional mutual information I(·;·|H_{t−1}) needs regular conditional distributions (published condMutualInfo); finite, countable and Euclidean action/outcome sets are all standard Borel
--   - encoding: measurability not stated → θ, W_t, ξ, ζ measurable; g, every ψ_t and f jointly measurable (IsModel, IsBenchmark); reason: standing convention that makes A_t, Y_t, Ã random variables; without it Measure.map is the zero measure
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, proof of Theorem 1, p.8 ("By the chain rule for mutual information, for any T," and the display)

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_SatisficingTS_IsModel
import Definitions.Def_SatisficingTS_IsBenchmark
import Definitions.Def_SatisficingTS_obs
import Definitions.Def_SatisficingTS_hist
open MeasureTheory ProbabilityTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace SatisficingTS

/-- **Finite-horizon information budget** (Russo & Van Roy, *Satisficing in Time-Sensitive Bandit
Learning*, arXiv:1803.02855v2, proof of Theorem 1, p.8: "By the chain rule for mutual information,
for any T, ∑_{t=0}^T I(Ã; (At, Yt) | Ht−1) = ⋯ = I(Ã; HT) ≤ ⋯ = I(Ã; θ)").

In the model of §2, for a benchmark `Ã = f(θ, ζ)` whose randomness `ζ` is independent of
`(θ, (W_t)_t, ξ)`, and for every `T ≥ 0`,
`∑_{t=0}^T I(Ã; (A_t, Y_t) | H_{t−1}) ≤ I(Ã; θ)`.

**Formalization Note.** `(A_t, Y_t) = obs ψ g θ W ξ t`; `H_{t−1} = hist ψ g θ W ξ t` (0-based,
`t` entries, empty for `t = 0`). Information quantities in `ℝ≥0∞`, nats. -/
theorem sum_condMutualInfo_le_mutualInfo
    {Ω Θ 𝒲 Ξ 𝒵 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace 𝒲]
    [MeasurableSpace Ξ] [MeasurableSpace 𝒵]
    [MeasurableSpace 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (g : 𝒜 → Θ → 𝒲 → 𝒴)
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (hmodel : IsModel P θ W ξ g ψ)
    (ζ : Ω → 𝒵) (f : Θ → 𝒵 → 𝒜) (hbench : IsBenchmark P θ W ξ ζ f)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1),
        condMutualInfo P (fun ω => f (θ ω) (ζ ω)) (obs ψ g θ W ξ t) (hist ψ g θ W ξ t) ≤
      mutualInfo P (fun ω => f (θ ω) (ζ ω)) θ := by sorry

end SatisficingTS
