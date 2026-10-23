-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_eq_14
-- name    : SpeedFactory.BreakEven.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:58.250152+00:00
-- url     : https://prove2.me/theorems/96d85c36-ae58-47f9-becd-74fe68d3ae43
-- title:
--   §3 (14), p. 9 — under TBS-POUT with iid normal demand, i_t and q_t are normal with σ²_i = σ²/(1 − α²) and σ²_q = σ²(1 − α)/(1 + α)
-- statement:
--   Consider the TBS-POUT system with allocation $\gamma\in[0,1]$, smoothing parameter $\alpha\in(-1,1)$, safety stock $i^\star$ and deterministic initial inventory $i_0$. The demand is iid $N(\mu,\sigma)$ and the model satisfies the standing assumptions. Let $i_t$ be the inventory and $q_t$ the local order of period $t$. Then:
--
--   1. in every period, $i_t$ and $q_t$ are normally distributed;
--   2. $\mathbb E[i_t]\to i^\star$ and $\mathbb E[q_t]\to\mu\gamma$;
--   3. the variances converge to the values (14):
--   $$\operatorname{Var}(i_t)\to\sigma_i^2=\sigma^2\Big(\frac{1}{1-\alpha^2}\Big),\qquad \operatorname{Var}(q_t)\to\sigma_q^2=\sigma^2\Big(\frac{1-\alpha}{1+\alpha}\Big).$$
--
--   These variances feed the newsvendor optimizations of Proposition 1.
--
--   **Formalization Note** The paper allows $\alpha=1$, where $\sigma_i$ is infinite; $\alpha\in(-1,1)$ is assumed. At $t=0$ the inventory is the deterministic $i_0$, a degenerate normal law.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 9, §3, (14)

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory Filter

namespace SpeedFactory.BreakEven

/-- The TBS-POUT inventory and local-order variances under iid demand.
Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 9, §3, (14), with the sentence before Proposition 1 (p. 9) on normality.

Under iid `N(µ, σ)` demand, for every allocation `γ ∈ [0, 1]`, smoothing `α ∈ (−1, 1)`, safety
stock `i⋆` and initial inventory `i_0`: the inventory `i_t` and the local order `q_t` are
normally distributed in every period, their means converge to `i⋆` and `µγ`, and their
variances converge to `σ²_i = σ²/(1 − α²)` and `σ²_q = σ²(1 − α)/(1 + α)`.

**Formalization Note.** `α ∈ (−1, 1)` (the paper's `α = 1` makes `σ_i` infinite). Normality is
stated as `HasLaw X (gaussianReal (E X) (Var X))`; at `t = 0` the inventory is the deterministic
`i_0`, a degenerate Gaussian. -/
theorem eq_14 (M : Model) (hM : M.Standing) {γ α : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (iStar i0 : ℝ) :
    Tendsto (fun t => variance (invTBS M γ α iStar i0 d t) P) atTop (nhds (sigmaI M α ^ 2)) ∧
    Tendsto (fun t => variance (qTBS M γ α iStar i0 d t) P) atTop (nhds (sigmaQ M α ^ 2)) ∧
    Tendsto (fun t => ∫ ω, invTBS M γ α iStar i0 d t ω ∂P) atTop (nhds iStar) ∧
    Tendsto (fun t => ∫ ω, qTBS M γ α iStar i0 d t ω ∂P) atTop (nhds (M.μ * γ)) ∧
    (∀ t, HasLaw (invTBS M γ α iStar i0 d t)
      (gaussianReal (∫ ω, invTBS M γ α iStar i0 d t ω ∂P)
        ⟨variance (invTBS M γ α iStar i0 d t) P, variance_nonneg _ _⟩) P) ∧
    (∀ t, HasLaw (qTBS M γ α iStar i0 d t)
      (gaussianReal (∫ ω, qTBS M γ α iStar i0 d t ω ∂P)
        ⟨variance (qTBS M γ α iStar i0 d t) P, variance_nonneg _ _⟩) P) := by sorry

end SpeedFactory.BreakEven
