-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_stationary_shift_release_budget
-- name    : TightReleaseSchedules.Stationary.stationary_shift_release_budget
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:45:42.526858+00:00
-- url     : https://prove2.me/theorems/b53628e0-9987-4718-8aaf-ed2522dfd9d1
-- title:
--   Theorem 4.1 — Stationary shift with a release budget
-- statement:
--   Let $T,d\ge1$ and $B\ge0$ be integers, let $\theta_0\in\mathbb R^d$ be arbitrary and known, and let $0<\Delta\le1$. An unknown deterministic stationary target $\theta$ ranges over the full closed ball $\|\theta-\theta_0\|_2\le\Delta$. The learner observes independent Gaussian regression rows with unit label noise and may replace its deployed predictor at most $B$ times on every realization. It has unrestricted monitoring, computation, retained history and independent randomization. Define $m=T\Delta^2/d$ and $\Lambda_B$ as in equation (1). Then
--
--   $$
--   R_T^*(B;\Delta,0)\le5d\Lambda_B(m).
--   $$
--
--   Algorithm 1, with the release count specified in Section 4.1, is admissible and uses deterministic dates, and its worst-case risk is at most the same $5d\Lambda_B(m)$. The reverse inequality
--
--   $$
--   R_T^*(B;\Delta,0)\ge2^{-27}d\Lambda_B(m)
--   $$
--
--   holds if $m<256$, or if $m\ge256$ and either $B+1\ge\log m$ or $d\ge1+2\log_2\log_2m$. No dimension or release-regime restriction is needed for the upper bound. The lower bound includes all randomized, adaptively timed release policies. Finally,
--
--   $$
--   B=0\quad\Longrightarrow\quad R_T^*(0;\Delta,0)=T\Delta^2/2.
--   $$
--
--   This theorem compares the actual deterministic geometric release policy with the unrestricted causal minimax problem, with the source's explicit constants and lower-bound regimes.
--
--   Differences from the source:
--   - encoding: positive integer T,d, nonnegative integer B and Euclidean observations → natural T,d,B with explicit T,d positivity, EuclideanSpace on Fin d and rows on Fin T; reason: every source integer instance occurs with source round t represented by index t-1
--   - encoding: infimum over all randomized causal policies of the worst-target expected half-squared loss → a set infimum over arbitrary independent measurable seed spaces and admissible policies, with ENNReal risk; reason: the policy class is unrestricted and infinite losses are represented without exclusions or default zeros
--   - encoding: the upper bound uses the deterministic grid of Algorithm 1 → admissibility, static dates and the worst-risk guarantee of the actual defined geometricPolicy are conjuncts; reason: the algorithm is evaluated directly, including rounding, deduplication, closed-ball projection and the zero-release branch
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Theorem 4.1 and Algorithm 1, printed p.8, PDF p.9; equation (1), printed p.1, PDF p.2; proof printed pp.9–13, PDF pp.10–14

import Definitions.Def_TightReleaseSchedules_Stationary_geometric_algorithm

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary

/-- Theorem 4.1, including Algorithm 1 and the exact zero-release risk. -/
theorem stationary_shift_release_budget (T d B : ℕ) (hT : 0 < T) (hd : 0 < d)
    (θ₀ : Vector d) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) :
    minimaxRisk T d B θ₀ Δ ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) ∧
    IsCausal (geometricPolicy T d B θ₀ Δ) ∧
    HasDeterministicDates (geometricPolicy T d B θ₀ Δ) ∧
    worstRisk θ₀ Δ (geometricPolicy T d B θ₀ Δ) ≤
      ENNReal.ofReal (5 * (d : ℝ) * releaseRate B (effectiveHorizon T d Δ)) ∧
    (lowerBoundRegime T d B Δ →
      ENNReal.ofReal ((2 : ℝ) ^ (-27 : ℤ) * (d : ℝ) *
        releaseRate B (effectiveHorizon T d Δ)) ≤ minimaxRisk T d B θ₀ Δ) ∧
    (B = 0 → minimaxRisk T d B θ₀ Δ = ENNReal.ofReal ((T : ℝ) * Δ ^ 2 / 2)) := by sorry

end TightReleaseSchedules.Stationary
