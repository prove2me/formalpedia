-- Prove2me | Theorems.Thm_RandomRateMSQ_theorem_5_martingale_limits
-- name    : RandomRateMSQ.theorem_5_martingale_limits
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:24.777621+00:00
-- url     : https://prove2.me/theorems/312ffadc-79bc-4421-a68c-f20747899484
-- title:
--   Proof of Theorem 5 — $\hat M^n_1\Rightarrow\sqrt{\bar\mu}\,W_2$ and $\hat M^n_2\to0$ (corrected: $\sqrt{\bar\mu}$ for $\bar\mu$)
-- statement:
--   Under the model and Assumptions 1 and 2:
--
--   1. the scaled service martingales converge in distribution in $D_{\mathbb R}[0,\infty)$ with the $J_1$ topology,
--   $$
--   \hat M^n_1\Rightarrow\sqrt{\bar\mu}\,W_2,
--   $$
--   with $W_2$ a standard Brownian motion;
--   2. the scaled abandonment martingales vanish uniformly on compacts in probability: $P\big(\sup_{t\le T}|\hat M^n_2(t)|>\delta\big)\to0$ for every $T\ge0$ and $\delta>0$.
--
--   Together with the arrival limit these give the Brownian noise of the limit equation.
--
--   Differences from the source:
--   - correction: M̂ⁿ₁(t) ⇒ µ̄ W₂(t) → M̂ⁿ₁ ⇒ √µ̄ W₂; reason: the page's own computation ⟨M̂ⁿ₁⟩ₜ → µ̄ t gives variance µ̄ t; with all rates 2 and Poisson arrivals the Erlang-A limit (√(2µ) = 2) contradicts the printed constant
--   - reading: M̂ⁿ₂(t) →p 0 → sup_{t≤T}|M̂ⁿ₂(t)| → 0 in probability for every T; reason: the stronger of the possible readings (process convergence to 0 uniformly on compacts), the one the proof of Theorem 5 needs
--   - encoding: weak convergence of laws (⇒) → coupling form: copies on one probability space converging almost surely; reason: equivalent by the Skorokhod representation theorem on Polish spaces; the form of public PuhaWardFluid.Limit.ConvInDist
--   - reading: non-anticipating routing: the server is chosen based on the information available so far (p.5) → a filtration G containing the system's past, with the potential completions and the abandonment clock after t independent of G_t (the latter again unit Poisson) and the interarrival times after the one in progress independent of G_t; reason: the page gives a one-line description; this is the standard formalization, it admits every routing rule that uses the past and independent randomization, and it assumes no consequence (the service martingale is proved, not assumed)
--   - generalization: exponential patience with rate γ (γ > 0) → γ ≥ 0; reason: γ = 0 is the model without abandonment (Atar's setting); γ enters the proof only through M̂ⁿ₂ and a Lipschitz drift; the statement specializes to γ > 0
--   - reading: interarrival times uⁿᵢ i.i.d. with mean 1 (p.5) → law F_u with mean 1 and finite second moment; reason: the page's model presupposes it: var(uⁿₖ) enters Theorem 5 through c²_a (p.17), and the proofs apply the functional central limit theorem for renewal processes (pp.7, 8, 18), which needs a finite variance
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, proof of Theorem 5, p.18

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **The martingale limits in the proof of Theorem 5** (Büke–Qin, arXiv:1905.04198v1, p.18),
with the constant corrected: under the model and Assumptions 1 and 2,
1. `M̂ⁿ₁ ⇒ √µ̄ W₂` in `D_ℝ[0, ∞)` with the `J₁` topology, `W₂` a standard Brownian motion;
2. `M̂ⁿ₂ →p 0` uniformly on compacts: `P(sup_{t≤T} |M̂ⁿ₂(t)| > δ) → 0` for all `T`, `δ > 0`.

**Formalization Note (correction).** p.18 prints `M̂ⁿ₁(t) ⇒ µ̄ W₂(t)`; its own computation
`⟨M̂ⁿ₁⟩ₜ → µ̄ t` gives `√µ̄ W₂`. Convergence in distribution is public
`PuhaWardFluid.Limit.ConvInDist` (coupling form). -/
theorem theorem_5_martingale_limits {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat)
    (hA2 : Assumption2 P sys) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : ℝ≥0 → Ω' → ℝ),
      IsBrownianReal W P' ∧
      PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P (fun n => M1hat (sys n)) P'
        (fun ω t => Real.sqrt (muBar F) * W t ω)) ∧
    ∀ T : ℝ≥0, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | ENNReal.ofReal δ <
      ⨆ (t : ℝ≥0) (_ : t ≤ T), ENNReal.ofReal |M2hat γ (sys n) ω t|}) atTop (𝓝 0) := by sorry

end RandomRateMSQ
