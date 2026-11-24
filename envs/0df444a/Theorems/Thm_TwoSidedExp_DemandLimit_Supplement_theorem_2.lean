-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_theorem_2
-- name    : TwoSidedExp.DemandLimit.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:23:23.538607+00:00
-- url     : https://prove2.me/theorems/862914cb-5195-44cc-8fac-020e9d532b73
-- title:
--   Theorem 2 (companion theorem; not used in the proof of the goal) — time-uniform O(1/N) finite-market approximation
-- statement:
--   Fix the standing model M and λ,τ > 0. For each N, consider the N-listing chain of §3 with counts m^(N)(θ), positive arrival rates λ_γ^(N) and positive outside options ϵ_γ^(N). Assume m^(N)(θ)/N → ρ(θ), λ_γ^(N)/N → λφ_γ and ϵ_γ^(N)/N → ϵ_γ. Start at any deterministic feasible state σ₀^(N) whose normalized state converges to ŝ ∈ S. Let s_t be the solution of (8) starting at ŝ. For every δ > 0 and u > 0,
--
--   $$\mathbb P_N\!\left[\sup_{0\le t\le u}\|Y_t^{(N)}-s_t\|>\delta\right]=O(1/N)\quad(N\to\infty),\qquad Y_t^{(N)}=\sigma_t^{(N)}/N.$$
--
--   The O-constant and the eventual size threshold may depend on δ, u, the model and all its sequences. This states the paper's quantitative finite-market approximation, rather than convergence in probability alone.
--
--   **Formalization Note** The norm is the finite-coordinate sup norm. Each size may have a different probability space. The chains have the generator (3)–(5), the published general CTMC finite-dimensional law, measurable coordinates and right-continuous paths. The event is expressed by existence of a time in [0,u] and measured by outer probability, which is ordinary probability for these paths. No approximation bound is assumed in the chain law.
--
--   Differences from the source:
--   - reading: The results use the standing marketplace assumptions of §3. → The published Model.Standing and λ,τ > 0 are explicit premises.; reason: This exposes positivity, normalizations, probability bounds and positive holding rates already implicit in the model; its unit-sum clauses exclude empty type spaces.
--   - encoding: The source uses trajectories on t ≥ 0. → Coordinate right derivatives at zero and derivatives on [0,∞) are used; uniqueness compares only nonnegative times.; reason: Negative-time extensions have no mathematical meaning for this initial-value problem.
--   - encoding: The chain is the continuous-time Markov process of §3, and the event uses a time supremum. → Its exact finite-dimensional law and right-continuous paths are explicit; the event is existential in time and uses outer probability.; reason: This is the source jump-process law, with no restriction on convergence speed; right-continuity reduces the supremum to rational times together with the endpoint.
--   - reading: §3 uses total arrivals λ^(N)/N → λ and shares λ_γ^(N)/λ^(N) → φ_γ. → The assumptions use λ_γ^(N)/N → λφ_γ, exactly as Theorem 2 does.; reason: For finitely many positive-rate types with shares summing to one, these formulations are equivalent.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. 13 (PDF 13), Theorem 2

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Normalized

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Theorem 2 (12), p. 13. The probability is the outer probability of the uncountable
supremum event; on right-continuous paths this is the usual measurable event. -/
theorem theorem_2 {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau)
    (F : (N : ℕ) → FiniteMarket Γ Θ N)
    (hm : ∀ θ, Tendsto (fun N => ((F N).m θ : ℝ) / N) atTop (𝓝 (M.sys.ρ θ)))
    (heps : ∀ γ, Tendsto (fun N => (F N).outside γ / N) atTop (𝓝 (M.sys.eps γ)))
    (harrival : ∀ γ, Tendsto (fun N => (F N).arrival γ / N) atTop (𝓝 (lam * M.sys.φ γ)))
    (σ₀ : (N : ℕ) → MarketState (F N)) (s₀ : Θ → ℝ)
    (hinit : Tendsto (fun N => normalized (F N) (σ₀ N)) atTop (𝓝 s₀))
    (Ω : ℕ → Type) [mΩ : ∀ N, MeasurableSpace (Ω N)]
    (μ : (N : ℕ) → Measure (Ω N)) [hμ : ∀ N, IsProbabilityMeasure (μ N)]
    (X : (N : ℕ) → ℝ → Ω N → MarketState (F N))
    (hchain : ∀ N, MarketChain (μ N) M hM (F N) tau (σ₀ N) (X N))
    (s : ℝ → Θ → ℝ) (hs : Trajectory M.sys lam tau s) (hsinit : s 0 = s₀)
    (δ u : ℝ) (hδ : 0 < δ) (hu : 0 < u) :
    Asymptotics.IsBigO atTop
      (fun N => (μ N).real {ω | ∃ t ∈ Set.Icc 0 u,
        δ < ‖normalized (F N) (X N t ω) - s t‖})
      (fun N : ℕ => (1 : ℝ) / N) := by sorry

end TwoSidedExp.DemandLimit.Supplement
