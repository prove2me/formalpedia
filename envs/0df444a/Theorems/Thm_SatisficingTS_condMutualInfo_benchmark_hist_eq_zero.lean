-- Prove2me | Theorems.Thm_SatisficingTS_condMutualInfo_benchmark_hist_eq_zero
-- name    : SatisficingTS.condMutualInfo_benchmark_hist_eq_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:27.348722+00:00
-- url     : https://prove2.me/theorems/36e626d1-51ae-4a0b-9252-4010d740bc24
-- title:
--   Proof of Theorem 1, p.8 — $I(\tilde A;\mathcal H_T\mid\theta)=0$: given $\theta$ the benchmark is independent of the history (corrected: benchmark randomness independent of the policy's)
-- statement:
--   Work in the model of §2 with a policy $\psi$, and let $\tilde A=f(\theta,\zeta)$ be a benchmark action whose randomness $\zeta$ is independent of $(\theta,(W_t)_{t\ge0},\xi)$. Then for every $T\ge0$
--   $$
--   I\bigl(\tilde A;\mathcal H_T\mid\theta\bigr)=0,
--   $$
--   that is, conditioned on $\theta$, the benchmark $\tilde A$ is independent of the history $\mathcal H_T=(A_0,Y_0,\dots,A_T,Y_T)$.
--
--   This is the last equality of the display in the proof of Theorem 1; it is what makes the history carry no more information about $\tilde A$ than $\theta$ does.
--
--   Differences from the source:
--   - correction: Ã = f(θ, ξ) with ξ independent of the disturbances, ξ being the paper's notation for the policy's exogenous randomness (§2, p.5) → Ã = f(θ, ζ) with the benchmark's randomness ζ independent of (θ, (W_t)_t, ξ) (IsBenchmark); reason: with the policy's ξ shared the theorem is false: θ constant, actions [0,1] ∪ {z₀, z₁} with µ = 1 on [0,1] and µ(z₀) = µ(z₁) = 0, noiseless Y_t = µ(A_t), ξ ~ Unif[0,1], D = 0, Ã = ξ, and the policy plays z_{b_t(ξ)} (b_t the t-th binary digit of ξ); then I(Ã;θ) = 0, I_t = log 2, E[R̃ − R_t] = 1, Γ = 1/log 2, so the bound is 0 while SRegret = 1/(1−α)
--   - reading: I(Ã; F_T | θ) → I(Ã; H_T | θ); reason: misprint: F_T is not defined; the display concerns H_T
--   - encoding: conditioned on θ, Ã is independent of H_T → condMutualInfo P Ã H_T θ = 0; reason: the conditional mutual information vanishes exactly when the joint law equals the conditionally independent one; it is the display's own form
--   - encoding: H_{t−1} = (A_0, Y_0, …, A_{t−1}, Y_{t−1}), H_T → hist ψ g θ W ξ t (t entries), H_T = hist … (T+1); reason: 0-based indexing of the same tuple; no instance changes
--   - encoding: action set A and outcome set Y arbitrary → standard Borel, nonempty measurable spaces; reason: the conditional mutual information I(·;·|H_{t−1}) needs regular conditional distributions (published condMutualInfo); finite, countable and Euclidean action/outcome sets are all standard Borel
--   - encoding: measurability not stated → θ, W_t, ξ, ζ measurable; g, every ψ_t and f jointly measurable (IsModel, IsBenchmark); reason: standing convention that makes A_t, Y_t, Ã random variables; without it Measure.map is the zero measure
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, proof of Theorem 1, p.8 ("where the final inequality uses that, conditioned on θ, Ã is independent of HT"; display line I(Ã; θ) + I(Ã; F_T|θ) = I(Ã; θ))

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

/-- **Conditioned on θ, the benchmark is independent of the history** (Russo & Van Roy,
*Satisficing in Time-Sensitive Bandit Learning*, arXiv:1803.02855v2, proof of Theorem 1, p.8:
"the final inequality uses that, conditioned on θ, Ã is independent of HT", which is the last line
`I(Ã; F_T | θ) = 0` of the display, `F_T` being a misprint for `H_T`).

In the model of §2, for a benchmark `Ã = f(θ, ζ)` whose randomness `ζ` is independent of
`(θ, (W_t)_t, ξ)`, and for every `T ≥ 0`, `I(Ã; H_T | θ) = 0`.

**Formalization Note.** 0-based history: the paper's `H_T` is `hist ψ g θ W ξ (T + 1)`.
Conditional mutual information is the published `ThompsonTutorial.InfoRatio.condMutualInfo`
(`ℝ≥0∞`, nats); its vanishing is conditional independence of `Ã` and `H_T` given `θ`. -/
theorem condMutualInfo_benchmark_hist_eq_zero
    {Ω Θ 𝒲 Ξ 𝒵 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace 𝒲]
    [MeasurableSpace Ξ] [MeasurableSpace 𝒵]
    [MeasurableSpace 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (g : 𝒜 → Θ → 𝒲 → 𝒴)
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (hmodel : IsModel P θ W ξ g ψ)
    (ζ : Ω → 𝒵) (f : Θ → 𝒵 → 𝒜) (hbench : IsBenchmark P θ W ξ ζ f)
    (T : ℕ) :
    condMutualInfo P (fun ω => f (θ ω) (ζ ω)) (hist ψ g θ W ξ (T + 1)) θ = 0 := by sorry

end SatisficingTS
