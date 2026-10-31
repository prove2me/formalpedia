-- Prove2me | Theorems.Thm_SatisficingTS_sRegret_le_sqrt_infoRatio_mul_mutualInfo
-- name    : SatisficingTS.sRegret_le_sqrt_infoRatio_mul_mutualInfo
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:31.717071+00:00
-- url     : https://prove2.me/theorems/11dac4ee-5df2-4c84-8146-3e414d0820c7
-- title:
--   Theorem 1 — every policy's satisficing regret is at most $\sqrt{\Gamma(\tilde A,\psi)\,I(\tilde A;\theta)/(1-\alpha^2)}$ (corrected: benchmark randomness independent of the policy's)
-- statement:
--   Work in the model of §2: a parameter $\theta$, iid disturbances $W_t$ independent of $\theta$, a system function $g$ with outcomes $Y_t=g(A_t,\theta,W_t)$, a reward function $R$, and a policy $\psi$ that chooses $A_t=\psi_t(\mathcal H_{t-1},\xi)$ using its own randomness $\xi$. Let $\alpha\in[0,1)$ and $D\ge0$, and let $\tilde A=f(\theta,\zeta)$ be a benchmark action whose randomness $\zeta$ is independent of $(\theta,(W_t)_{t\ge0},\xi)$ and whose expected reward is within $D$ of optimal:
--   $$
--   \mathbb E[\mu(\tilde A,\theta)]\ \ge\ \mathbb E[R^*]-D .
--   $$
--   Assume the rewards make $\mu$, $R^*$, $\tilde R=\mu(\tilde A,\theta)$, $R_t$ and the satisficing regret well defined (integrability of $R(g(a,\theta,\cdot))$, of $R^*$, $\tilde R$ and $R_t$, $\sup_a\mu(a,\theta)<\infty$ almost surely, and $\mathbb E[\sum_t\alpha^t|R^*-D-R_t|]<\infty$), and that $\Gamma(\tilde A,\psi)<\infty$ and $I(\tilde A;\theta)<\infty$. Then
--   $$
--   \mathrm{SRegret}(\alpha,\psi,D)\ \le\ \sqrt{\frac{\Gamma(\tilde A,\psi)\,I(\tilde A;\theta)}{1-\alpha^2}} .
--   $$
--
--   The bound holds for every policy and every benchmark at once. It replaces the entropy of the optimal action in earlier information-ratio analyses by $I(\tilde A;\theta)$, the information a decision-maker must acquire to implement $\tilde A$, which stays finite in many-armed and continuous problems where the entropy of the optimal action does not.
--
--   **Formalization Note** Information quantities are in $[0,\infty]$ and in nats; $\Gamma_t$ uses $x/0=\infty$ ($x>0$) and $0/0=0$. Histories are 0-based. $\mu(a,\theta)$ is the integral of $R(g(a,\theta,\cdot))$ against the law of $W_0$.
--
--   Differences from the source:
--   - reading: E[µ(Ã, θ)] ≥ R∗ − D → E[µ(Ã, θ)] ≥ E[R*] − D; reason: R* = sup_a µ(a, θ) is random; §3 (p.6) states the performance loss as E[R* − R̃] and constraint (7), p.10, as E[R* − µ(Ã,θ)] ≤ D; the pointwise reading µ(Ã,θ) ≥ R* − D a.s. implies this one, so this is the stronger theorem
--   - correction: Ã = f(θ, ξ) with ξ independent of the disturbances, ξ being the paper's notation for the policy's exogenous randomness (§2, p.5) → Ã = f(θ, ζ) with the benchmark's randomness ζ independent of (θ, (W_t)_t, ξ) (IsBenchmark); reason: with the policy's ξ shared the theorem is false: θ constant, actions [0,1] ∪ {z₀, z₁} with µ = 1 on [0,1] and µ(z₀) = µ(z₁) = 0, noiseless Y_t = µ(A_t), ξ ~ Unif[0,1], D = 0, Ã = ξ, and the policy plays z_{b_t(ξ)} (b_t the t-th binary digit of ξ); then I(Ã;θ) = 0, I_t = log 2, E[R̃ − R_t] = 1, Γ = 1/log 2, so the bound is 0 while SRegret = 1/(1−α)
--   - encoding: α ∈ [0,1] (p.5) → 0 ≤ α < 1; reason: at α = 1 the printed right side is 0/0 (Γ carries the factor 1 − α² = 0 and the bound divides by it)
--   - encoding: Γ(Ã,ψ) and I(Ã;θ) unrestricted → Γ(Ã,ψ) ≠ ⊤, I(Ã;θ) ≠ ⊤, and the right side computed with their real values; reason: with an infinite factor the printed right side is +∞ (the bound is empty) or the undefined 0·∞
--   - encoding: rewards unrestricted; µ, R*, SRegret written as expectations and a supremum → for every a, R(g(a,θ,·)) integrable for almost every value of θ; a ↦ µ(a,θ) bounded above a.s.; R*, R̃, every R_t integrable; ∫⁻ ∑ α^t|R* − D − R_t| < ∞; reason: these make the paper's expectations, supremum and series defined (Lean returns 0 otherwise); bounded rewards with α < 1 satisfy them
--   - encoding: µ(a, θ) = E[R(g(a, θ, W_t)) | θ] → ∫ R(g(a, θ, w)) d(law of W_0)(w); reason: a version of the conditional expectation, since the W_t are identically distributed and independent of θ
--   - encoding: E[R̃ − R_t] in Γ_t → E[R̃] − E[R_t]; reason: equal under the integrability hypotheses
--   - encoding: H_{t−1} = (A_0, Y_0, …, A_{t−1}, Y_{t−1}), H_T → hist ψ g θ W ξ t (t entries), H_T = hist … (T+1); reason: 0-based indexing of the same tuple; no instance changes
--   - encoding: action set A and outcome set Y arbitrary → standard Borel, nonempty measurable spaces; reason: the conditional mutual information I(·;·|H_{t−1}) needs regular conditional distributions (published condMutualInfo); finite, countable and Euclidean action/outcome sets are all standard Borel
--   - encoding: measurability not stated → θ, W_t, ξ, ζ measurable; g, every ψ_t and f jointly measurable (IsModel, IsBenchmark); reason: standing convention that makes A_t, Y_t, Ã random variables; without it Measure.map is the zero measure
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, Theorem 1, p.8

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_SatisficingTS_IsModel
import Definitions.Def_SatisficingTS_IsBenchmark
import Definitions.Def_SatisficingTS_obs
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
import Definitions.Def_SatisficingTS_supReward
import Definitions.Def_SatisficingTS_sRegret
import Definitions.Def_SatisficingTS_infoRatio
open MeasureTheory ProbabilityTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace SatisficingTS

/-- **Theorem 1 (general satisficing regret bound)** (Russo & Van Roy, *Satisficing in
Time-Sensitive Bandit Learning*, arXiv:1803.02855v2, Theorem 1, p.8): "For any policy ψ, any
D ≥ 0 and any Ã = f(θ, ξ) where ξ is independent of the disturbances (Wt)t∈N0, if
E[µ(Ã, θ)] ≥ R∗ − D, then SRegret(α, ψ, D) ≤ √( Γ(Ã, ψ) I(Ã; θ) / (1 − α²) )."

In the model of §2 (`IsModel`), for every discount factor `α ∈ [0, 1)`, every `D ≥ 0`, every
(measurable) policy `ψ` and every benchmark `Ã = f(θ, ζ)` whose randomness `ζ` is independent of
`(θ, (W_t)_t, ξ)` and which satisfies `E[µ(Ã, θ)] ≥ E[R*] − D`: if the rewards make `µ`, `R*`,
`R̃`, `R_t` and `SRegret` well defined and `Γ(Ã, ψ)`, `I(Ã; θ)` are finite, then
`SRegret(α, ψ, D) ≤ √(Γ(Ã, ψ) · I(Ã; θ) / (1 − α²))`.

**Formalization Note.**
* 0-based histories: `H_{t−1} = hist ψ g θ W ξ t`, `(A_t, Y_t) = obs ψ g θ W ξ t`.
* `Γ(Ã, ψ)` (display (4)) and the mutual information are in `ℝ≥0∞`, nats; `Γ_t` uses
  `x / 0 = ⊤` (`x > 0`) and `0 / 0 = 0`. Both are assumed finite and converted to reals.
* `µ(a, θ)` is the integral of `R(g(a, θ, ·))` against the law of `W_0` (the published
  `ThompsonTutorial.InfoRatio.meanReward g R (P.map (W 0))`); for each action `a` it is assumed integrable for almost
  every value of `θ`, which is what makes `E[R(g(a, θ, W_t)) | θ]` defined.
* `α < 1`: at `α = 1` the printed right side is `0/0`.
* The benchmark's randomness `ζ` is independent of the policy's randomness `ξ` (correction:
  with a shared `ξ` the printed theorem is false).
* `E[µ(Ã, θ)] ≥ R* − D` is read as `E[µ(Ã, θ)] ≥ E[R*] − D` (`R*` is random). -/
theorem sRegret_le_sqrt_infoRatio_mul_mutualInfo
    {Ω Θ 𝒲 Ξ 𝒵 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace 𝒲]
    [MeasurableSpace Ξ] [MeasurableSpace 𝒵]
    [MeasurableSpace 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (g : 𝒜 → Θ → 𝒲 → 𝒴) (R : 𝒴 → ℝ)
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (hmodel : IsModel P θ W ξ g ψ)
    (ζ : Ω → 𝒵) (f : Θ → 𝒵 → 𝒜) (hbench : IsBenchmark P θ W ξ ζ f)
    (α D : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hD : 0 ≤ D)
    (hμ_int : ∀ a, ∀ᵐ ω ∂P, Integrable (fun w => R (g a (θ ω) w)) (P.map (W 0)))
    (hbdd : ∀ᵐ ω ∂P, BddAbove (Set.range fun a => meanReward g R (P.map (W 0)) a (θ ω)))
    (hRstar_int : Integrable (fun ω => supReward P W g R (θ ω)) P)
    (hRtilde_int : Integrable (fun ω => meanReward g R (P.map (W 0)) (f (θ ω) (ζ ω)) (θ ω)) P)
    (hRt_int : ∀ t, Integrable (fun ω => R (obs ψ g θ W ξ t ω).2) P)
    (hsum : ∫⁻ ω, ∑' t, ENNReal.ofReal
        (α ^ t * |supReward P W g R (θ ω) - D - R (obs ψ g θ W ξ t ω).2|) ∂P ≠ ⊤)
    (hgood : ∫ ω, supReward P W g R (θ ω) ∂P - D ≤
        ∫ ω, meanReward g R (P.map (W 0)) (f (θ ω) (ζ ω)) (θ ω) ∂P)
    (hΓ : infoRatio P θ W ξ g R ψ (fun ω => f (θ ω) (ζ ω)) α ≠ ⊤)
    (hI : mutualInfo P (fun ω => f (θ ω) (ζ ω)) θ ≠ ⊤) :
    sRegret P θ W ξ g R ψ α D ≤
      Real.sqrt ((infoRatio P θ W ξ g R ψ (fun ω => f (θ ω) (ζ ω)) α).toReal *
        (mutualInfo P (fun ω => f (θ ω) (ζ ω)) θ).toReal / (1 - α ^ 2)) := by sorry

end SatisficingTS
