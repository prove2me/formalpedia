-- Prove2me | Theorems.Thm_RandomRateMSQ_theorem_5_clt_limits
-- name    : RandomRateMSQ.theorem_5_clt_limits
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:00.58879+00:00
-- url     : https://prove2.me/theorems/1729c79e-facf-47f6-aeea-1775ef8d13cc
-- title:
--   Proof of Theorem 5 — $\hat A^n\Rightarrow\sqrt{\bar\mu\,\mathrm{var}\,u}\,W_1$ and $\hat\sigma^n\Rightarrow N(0,\mathrm{var}\,\tilde\mu)$ (corrected: constant and the sum in $\hat\sigma^n$)
-- statement:
--   Under the model and Assumption 1:
--
--   1. the scaled arrival processes converge in distribution in $D_{\mathbb R}[0,\infty)$ with the $J_1$ topology,
--   $$
--   \hat A^n=\frac{A^n(t)-\lambda_nt}{\sqrt n}\Rightarrow\sqrt{\bar\mu\,\mathrm{var}\,u}\;W_1,
--   $$
--   with $W_1$ a standard Brownian motion (renewal functional central limit theorem);
--   2. the scaled rate fluctuations converge in distribution,
--   $$
--   \hat\sigma^n=\frac{\sum_{k=1}^n(\tilde\mu^n_k-\bar\mu)}{\sqrt n}\Rightarrow\tilde\sigma\sim N(0,\mathrm{var}\,\tilde\mu)
--   $$
--   (central limit theorem).
--
--   The first gives the arrival part of the noise; the second gives the random drift $\beta=\hat\lambda-\tilde\sigma$ of the limit.
--
--   Differences from the source:
--   - correction: Âⁿ ⇒ c_a µ̄ W₁ with c²_a = var(u)/µ̄², i.e. √(var u) W₁ → Âⁿ ⇒ √(µ̄ var u) W₁; reason: Aⁿ(t) = N(λₙt) for the renewal process N of the mean-1 gaps, the renewal FCLT gives (N(λₙ·) − λₙ·)/√λₙ ⇒ √(var u) W and λₙ/n → µ̄; with Poisson arrivals the Erlang-A limit confirms √µ̄
--   - correction: σ̂ⁿ = (µ̃ⁿₖ − µ̄)/√n (free index k; tends to 0) → σ̂ⁿ = Σₖ(µ̃ⁿₖ − µ̄)/√n; reason: the sixth term of (3.2) forces the sum; without it the limit would be 0, not N(0, var µ̃)
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

/-- **The arrival and rate limits in the proof of Theorem 5** (Büke–Qin, arXiv:1905.04198v1,
p.18), with the constant corrected and the typo in `σ̂ⁿ` fixed: under the model and Assumption 1,
1. `Âⁿ = (Aⁿ(t) − λₙ t)/√n ⇒ √(µ̄ var u) W₁` in `D_ℝ[0, ∞)` with `J₁`, `W₁` a standard Brownian
   motion (renewal functional central limit theorem);
2. `σ̂ⁿ = Σ_{k=1}^{n} (µ̃ⁿₖ − µ̄)/√n ⇒ σ̃ ~ N(0, var µ̃)` (central limit theorem).

**Formalization Note (correction).** p.18 prints `Âⁿ ⇒ cₐ µ̄ W₁` with `c²ₐ = var u/µ̄²`, i.e.
`√(var u) W₁`; the arrival counts are `N(λₙ t)` for the renewal process `N` of the mean-1 gaps and
`λₙ/n → µ̄`, so the limit is `√(µ̄ var u) W₁`. p.18 prints `σ̂ⁿ = (µ̃ⁿₖ − µ̄)/√n` without the sum.
Convergence of `σ̂ⁿ` is in coupling form, with the limit the identity on `(ℝ, N(0, var µ̃))`. -/
theorem theorem_5_clt_limits {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : ℝ≥0 → Ω' → ℝ),
      IsBrownianReal W P' ∧
      PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P
        (fun n => Ahat (lam n) (sys n)) P'
        (fun ω t => Real.sqrt (muBar F * varU Fu) * W t ω)) ∧
    ConvInDistCoupling P (fun n => sigmaHat F (sys n)) (gaussianReal 0 (varMu F).toNNReal) id := by sorry

end RandomRateMSQ
