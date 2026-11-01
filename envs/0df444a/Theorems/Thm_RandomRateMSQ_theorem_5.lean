-- Prove2me | Theorems.Thm_RandomRateMSQ_theorem_5
-- name    : RandomRateMSQ.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:29:23.048188+00:00
-- url     : https://prove2.me/theorems/29ade496-aa1f-450a-9bde-2436c7b6c05a
-- title:
--   Theorem 5 — the Halfin–Whitt scaled queue converges to a diffusion driven by the limiting fairness process (corrected: noise coefficient $\sqrt{\bar\mu(1+\mathrm{var}\,u)}$)
-- statement:
--   Let the systems $n=0,1,2,\dots$ satisfy the model: renewal arrivals at rate $\lambda_n$ with mean-1 interarrival times of finite variance $\mathrm{var}\,u$; $n$ exponential servers whose rates are i.i.d. with law $F$ on $(0,\infty)$, $\int\mu^2dF<\infty$, mean $\bar\mu$ and variance $\mathrm{var}\,\tilde\mu$; abandonment from the queue at rate $\gamma\ge0$; and any non-idling, non-anticipating, non-preemptive routing. Assume Assumptions 1 and 3 and fix the placeholder $\zeta$.
--
--   Suppose that $\tau^n_0\Rightarrow\tau_0$ and that the tuples $\big(\hat X^n(0),\hat\sigma^n,\hat N^n,(\tau^n_{\varepsilon_k},S^n_{\varepsilon_k}\eta^n)_k\big)$ converge jointly in distribution to $\big(\xi_0,\tilde\sigma,N,(\tau_{\varepsilon_k},S_{\varepsilon_k}\eta)_k\big)$, $\varepsilon_k=1/(k+1)$, where $\hat N^n=\hat A^n-\hat M^n_1-\hat M^n_2$; so $\eta$ is the limiting fairness process of Definition 1 and $\hat X^n(0)\Rightarrow\xi_0$ is Assumption 2. Normalize $\eta_t=\zeta$ at the times $t\le\tau_{\varepsilon_k}$ for all $k$, where Definition 1 does not determine it. Then on the limit space:
--
--   1. $\tilde\sigma$ is normal with mean $0$ and variance $\mathrm{var}\,\tilde\mu$;
--   2. $N=\sqrt{\bar\mu(1+\mathrm{var}\,u)}\;W$ for a standard Brownian motion $W$;
--   3. almost surely $t\mapsto\langle\!\langle\iota,\eta_t\rangle\!\rangle$ is finite and bounded on every $[0,T]$;
--   4. almost surely the equation
--   $$
--   \xi(t)=\xi_0+\sqrt{\bar\mu(1+\mathrm{var}\,u)}\,W(t)+\beta t+\langle\!\langle\iota,\eta_t\rangle\!\rangle\int_0^t\xi^-(s)\,ds-\gamma\int_0^t\xi^+(s)\,ds,\quad t\ge0,\qquad\beta=\hat\lambda-\tilde\sigma,
--   $$
--   has exactly one measurable solution bounded on every $[0,T]$;
--   5. the scaled processes converge in distribution, $\hat X^n\Rightarrow\xi$, in $D_{\mathbb R}[0,\infty)$ with the Skorokhod $J_1$ topology, where $\xi$ is the solution of 4.
--
--   The routing policy enters the diffusion limit only through the mean $\langle\!\langle\iota,\eta_t\rangle\!\rangle$ of the limiting fairness process.
--
--   Differences from the source:
--   - correction: noise (µ̄√(c²_a + 1))W with c²_a = var(u)/µ̄² → N = √(µ̄(1 + var u)) W; reason: counterexample: F = δ₂, Poisson arrivals (var u = 1), λₙ = 2n, γ = 1, Xⁿ(0) = n, ζ = δ₂ satisfies every assumption, ηⁿ ≡ δ₂, and the system is Erlang-A, whose limit (Garnett–Mandelbaum–Reiman 2002) has coefficient √(2µ) = 2, while the printed formula gives √5; the page's own limits (⟨M̂ⁿ₁⟩ → µ̄t, renewal FCLT) give √(µ̄(1 + var u))
--   - reading: ξ built from ξ₀ (Assumption 2), W, σ̃ ~ N(0, var µ̃) and the limiting fairness process η, each given by its own law → hypothesis: (X̂ⁿ(0), σ̂ⁿ, N̂ⁿ, (τⁿ_{ε_k}, Sⁿ_{ε_k}ηⁿ)_k) converges jointly in distribution to (ξ₀, σ̃, N, (τ_{ε_k}, S_{ε_k}η)_k), with N and σ̃ unconstrained; conclusion: σ̃ ~ N(0, var µ̃), N = √(µ̄(1 + var u)) W; reason: the law of ξ depends on the joint law of (ξ₀, σ̃, W, η), which the statement leaves open; the proof (p.18) uses the joint limit of Ξⁿ; the reading with independent limit objects is false (ξ₀ = σ̃ is possible); the identification of σ̃ and N is part of the conclusion, not assumed
--   - encoding: Assumption 2 (X̂ⁿ(0) ⇒ ξ₀) as a separate hypothesis → the first component of the joint hypothesis; reason: the joint hypothesis contains it; same instances
--   - reading: the limiting fairness process η (determined by Definition 1 only through its shifts S_εη) → η normalized to ζ at the times t ≤ τ_{ε_k} for every k; reason: Definition 1 leaves η unconstrained there; any limiting fairness process can be so normalized without changing its shifts, and on those times ∫₀ᵗξ⁻ = 0, so the equation does not change
--   - reading: ξ is the solution of (3.7) → conclusions 3 and 4: ⟨⟨ι, ηₜ⟩⟩ is a.s. finite and locally bounded, and (3.7) has a.s. exactly one measurable locally bounded solution; reason: the statement presupposes both; they are stated as conclusions, so nothing is assumed
--   - generalization: Definition 1 for every ε > 0 and τⁿ_ε ⇒ τ_ε for every ε ≥ 0 → the shifts and τ's only along ε_k = 1/(k + 1), plus τⁿ₀ ⇒ τ₀; reason: the paper reduces Definition 1 to any sequence ε_k → 0 (p.10) and its proof uses ε_k = 1/k only (p.18); the full family implies this one
--   - reading: G_P[0, ∞) with Skorokhod J1 defined by time reversal on [a, b] and extended to [0, ∞) 'in a similar manner' (p.3) → J1 for left-continuous paths via time changes of [0, ∞), uniform on compacts, Lévy–Prokhorov distance on P; reason: the printed definition is garbled (the domains do not match); on each [0, T] time changes commute with time reversal, and the global form is the standard extension (Whitt; public J1Tendsto)
--   - encoding: weak convergence of laws (⇒) → coupling form: copies on one probability space converging almost surely; reason: equivalent by the Skorokhod representation theorem on Polish spaces; the form of public PuhaWardFluid.Limit.ConvInDist
--   - reading: non-anticipating routing: the server is chosen based on the information available so far (p.5) → a filtration G containing the system's past, with the potential completions and the abandonment clock after t independent of G_t (the latter again unit Poisson) and the interarrival times after the one in progress independent of G_t; reason: the page gives a one-line description; this is the standard formalization, it admits every routing rule that uses the past and independent randomization, and it assumes no consequence (the service martingale is proved, not assumed)
--   - generalization: exponential patience with rate γ (γ > 0) → γ ≥ 0; reason: γ = 0 is the model without abandonment (Atar's setting); γ enters the proof only through M̂ⁿ₂ and a Lipschitz drift; the statement specializes to γ > 0
--   - reading: interarrival times uⁿᵢ i.i.d. with mean 1 (p.5) → law F_u with mean 1 and finite second moment; reason: the page's model presupposes it: var(uⁿₖ) enters Theorem 5 through c²_a (p.17), and the proofs apply the functional central limit theorem for renewal processes (pp.7, 8, 18), which needs a finite variance
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Theorem 5, p.17 (proof pp.17–19); Definition 1, p.10; Assumptions 1–3, pp.5, 7, 10

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_FairnessJointLimit
import Definitions.Def_RandomRateMSQ_SolvesLimitEq

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **Theorem 5** (Büke–Qin, arXiv:1905.04198v1, p.17), corrected and read jointly.

Let the systems `n = 0, 1, 2, …` satisfy the model (`IsModelSeq`: renewal arrivals with mean-1
gaps of finite variance, i.i.d. rates of law `F` on `(0, ∞)` with finite second moment, exponential
services and patience `γ ≥ 0`, any non-idling, non-anticipating, non-preemptive routing) and
Assumptions 1 and 3. Suppose `τⁿ₀ ⇒ τ₀` and that the tuples
`Θⁿ = (X̂ⁿ(0), σ̂ⁿ, N̂ⁿ, (τⁿ_{ε_k}, Sⁿ_{ε_k} ηⁿ)_{k})` converge jointly in distribution to
`Θ = (ξ₀, σ̃, N, (τ_{ε_k}, S_{ε_k} η)_{k})` (`FairnessJointLimit`; so `η` is the limiting fairness
process of Definition 1 and `X̂ⁿ(0) ⇒ ξ₀` is Assumption 2), with `η` equal to `ζ` at the times
Definition 1 leaves it unconstrained. Then, on the limit space:
1. `σ̃ ~ N(0, var µ̃)`;
2. `N = √(µ̄(1 + var u)) W` for a standard Brownian motion `W`;
3. almost surely `t ↦ ⟨⟨ι, ηₜ⟩⟩` is finite and bounded on every `[0, T]`;
4. almost surely the equation (3.7),
   `ξ(t) = ξ₀ + N(t) + (λ̂ − σ̃) t + ⟨⟨ι, ηₜ⟩⟩ ∫₀ᵗ ξ⁻(s) ds − γ ∫₀ᵗ ξ⁺(s) ds`, `t ≥ 0`,
   has exactly one measurable locally bounded solution;
5. `X̂ⁿ ⇒ ξ` in `D_ℝ[0, ∞)` with the `J₁` topology, for the solutions `ξ` of 4.

**Formalization Note.** (correction) The diffusion coefficient is `√(µ̄(1 + var u))`, not the
printed `µ̄ √(c²ₐ + 1)` (see `noiseCoeff`). (reading) The limit objects are a joint limit; their
joint law determines the law of `ξ` (p.18 uses the joint limit of `Ξⁿ`). The shift levels are
`ε_k = 1/(k + 1)` (p.10). Convergence in `D` is public `PuhaWardFluid.Limit.ConvInDist`. -/
theorem theorem_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (ζ : ProbabilityMeasure ℝ≥0) (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat)
    (hA3 : Assumption3 P ζ sys)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ξ₀ σ : Ω' → ℝ) (N : Ω' → ℝ≥0 → ℝ) (τ : ℕ → Ω' → ℝ≥0∞) (τ₀ : Ω' → ℝ≥0∞)
    (η : Ω' → ℝ≥0 → ProbabilityMeasure ℝ≥0)
    (hτ₀ : ConvInDistCoupling P (fun n => tau (sys n) 0) P' τ₀)
    (hjoint : FairnessJointLimit P (fun n => thetaN F (lam n) γ ζ (sys n)) P'
      (thetaLim ζ ξ₀ σ N τ η))
    (hη : ∀ ω (t : ℝ≥0), (∀ k, (t : ℝ≥0∞) ≤ τ k ω) → η ω t = ζ) :
    P'.map σ = gaussianReal 0 (varMu F).toNNReal ∧
    (∃ W : ℝ≥0 → Ω' → ℝ, IsBrownianReal W P' ∧
      ∀ᵐ ω ∂P', ∀ t, N ω t = noiseCoeff (muBar F) (varU Fu) * W t ω) ∧
    (∀ᵐ ω ∂P', ∀ T : ℝ≥0, ∃ K : ℝ≥0, ∀ t : ℝ≥0, t ≤ T → meanRate (η ω t) ≤ K) ∧
    (∀ᵐ ω ∂P', ∃! ξ : ℝ≥0 → ℝ, SolvesLimitEq (ξ₀ ω) (N ω) (lamHat - σ ω) γ
      (fun t => (meanRate (η ω t)).toReal) ξ) ∧
    ∃ ξ : Ω' → ℝ≥0 → ℝ,
      (∀ᵐ ω ∂P', SolvesLimitEq (ξ₀ ω) (N ω) (lamHat - σ ω) γ
        (fun t => (meanRate (η ω t)).toReal) (ξ ω)) ∧
      PuhaWardFluid.Limit.ConvInDist (fun a b : ℝ => dist a b) P (fun n => Xhat (sys n)) P' ξ := by sorry

end RandomRateMSQ
