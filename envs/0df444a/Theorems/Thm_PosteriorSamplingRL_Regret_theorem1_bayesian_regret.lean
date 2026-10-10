-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_theorem1_bayesian_regret
-- name    : PosteriorSamplingRL.Regret.theorem1_bayesian_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:03:07.002983+00:00
-- url     : https://prove2.me/theorems/4cf6db51-004a-4858-827e-6c82713aa1f9
-- title:
--   Theorem 1, p. 4 — PSRL: E[Regret(T, π^PS_τ)] ≤ C·τS√(AT log(SAT)) for an absolute constant C and every prior
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $S,A,\tau\ge1$ and consider finite MDPs with $S$ states, $A$ actions, horizon $\tau$, reward distributions supported on $[0,1]$ and a fixed initial state distribution $\rho$. Let $f$ be any prior on such MDPs, let $\theta\mapsto\mu^\theta$ be any measurable choice of an optimal policy for each MDP, and consider PSRL run on a true MDP $M^*$ drawn from $f$. Then for every $T\ge0$,
--   $$
--   \mathbb E\big[\mathrm{Regret}(T,\pi^{\mathrm{PS}}_\tau)\big]\le C\,\tau S\sqrt{AT\log(SAT)} .
--   $$
--
--   This is the Bayesian regret bound $\mathbb E[\mathrm{Regret}(T,\pi^{\mathrm{PS}}_\tau)]=O(\tau S\sqrt{AT\log(SAT)})$ of the paper. It holds for every prior, and it is the first such guarantee for an algorithm that is not based on optimism.
--
--   **Formalization Note** The $O(\cdot)$ is read as one absolute constant, quantified before $S$, $A$, $\tau$, the parameter space, the prior, the selector, the run and $T$; a constant allowed to depend on any of them would make the statement trivial, since the regret is at most $\lceil T/\tau\rceil\tau$. Appendix B's explicit constant $\sqrt{30}$ is not the formal claim: its derivation adds $\sqrt2+\sqrt{28}>\sqrt{30}$ and contains the corrections recorded in the milestones. No lower bound on $T$ and no condition on the prior are assumed; at $T=0$ both sides are $0$. The logarithm is natural. The PSRL run is the structure `PSRLRun`, with the standing model assumptions described there (reset from $\rho$, observed last transition, fresh sampling randomness, measurability).
-- source:
--   arXiv:1306.0940v5, Theorem 1, (1), p. 4

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Run

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- Theorem 1 (arXiv:1306.0940v5, p. 4). If `f` is the distribution of `M*`, the expected regret
of PSRL satisfies `E[Regret(T, π^PS_τ)] = O(τ S √(A T log(S A T)))`, with one absolute constant,
uniform in `S, A, τ`, the prior, the optimal-policy selector, the run and `T`. -/
theorem theorem1_bayesian_regret :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S A τ : ℕ), 1 ≤ S → 1 ≤ A → 1 ≤ τ →
      ∀ (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ), IsDist ρ →
      ∀ (f : Measure Θ) (sel : Θ → Policy S A τ), (∀ θ, IsOptimal F θ (sel θ)) → Measurable sel →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (R : PSRLRun F ρ f sel μ) (T : ℕ),
        ∫ ω, R.regret T ω ∂μ
          ≤ C * τ * S * Real.sqrt ((A : ℝ) * T * Real.log ((S : ℝ) * A * T)) := by sorry

end PosteriorSamplingRL.Regret
