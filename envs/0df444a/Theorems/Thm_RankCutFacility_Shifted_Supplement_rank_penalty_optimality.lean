-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_rank_penalty_optimality
-- name    : RankCutFacility.Shifted.Supplement.rank_penalty_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:21:30.887935+00:00
-- url     : https://prove2.me/theorems/025277e0-48ac-4aa3-a708-5e0bc48588c5
-- title:
--   Theorem 5.1 — Optimality of $\rho^*_D$ among deterministic rank penalties
-- statement:
--   A **deterministic rank-penalty algorithm** fixes in advance, for every horizon $n$, positive penalties $\lambda_{1,n},\dots,\lambda_{n,n}$ (no monotonicity, no upper bound, no dependence on the metric, costs, demands or history). At rank $t$ it selects $y\in\arg\min_y\{d(x,y)+\lambda_{t,n}f_y\}$ with a fixed tie order and opens $y$ iff $d(x,O_{t-1})\ge d(x,y)+\lambda_{t,n}f_y$, then connects $x$ to its nearest open facility. Let $\mu_D$ be the unique solution in $(0,1]$ of $A(\mu)=g(\mu)$ with $A(\mu)=1+e^{-(1+\mu)}/\mu$, $g(\mu)=\tfrac12\big(3+2\mu+\sqrt{(3+2\mu)^2+4}\big)$, $\rho^*_D=A(\mu_D)$ and $\delta_D=\mu_D\rho^*_D$.
--
--   **Theorem 5.1.** Every deterministic rank-penalty algorithm has random-order competitive ratio at least $\rho^*_D$: if $\mathbb E[\mathrm{ALG}]\le C\cdot\mathrm{OPT}$ for every finite metric in which every point is a feasible candidate, every positive cost function, every horizon and every demand multiset, then
--
--   $$C\ge\rho^*_D.$$
--
--   Consequently the infimum competitive ratio over the class is exactly $\rho^*_D\approx3.538$: the shifted schedule $\lambda_{t,n}=\min\{1,(t-1+\delta_D)/(\mu_D n)\}$ is positive and satisfies $\mathbb E[\mathrm{ALG}]\le\rho^*_D\,\mathrm{OPT}$ on every instance. The statement also certifies that $\mu_D$ exists and is unique.
--
--   This companion theorem shows that the mission's goal constant cannot be improved by any choice of scalar penalties depending only on rank and horizon.
--
--   Differences from the source:
--   - generalization: C-competitive on every instance under the algorithm's fixed tie order → C-competitive only on finite full-space instances (every point a candidate), with a tie order allowed to depend on the instance; reason: a weaker hypothesis, so the Lean statement implies the source's; the source states that the bound already holds on finite full-space metrics, and its instances have unique minimizers
--   - encoding: competitive ratio at least ρ*_D → every C for which the schedule is C-competitive satisfies ρ*_D ≤ C; reason: the competitive ratio is the infimum of such C (an infinite ratio admits no C)
--   - encoding: the infimum over the class is exactly ρ*_D, attained by Algorithm 1 at (µ_D, δ_D) → the shifted schedule at (muD, deltaD) is positive at every rank and satisfies E[ALG] ≤ ρ*_D · OPT on every instance; reason: together with the lower bound this is the infimum identity and its attainment
--   - encoding: µ_D, the unique solution in (0,1] of A(µ) = g(µ) → the canonical sInf of the solution set in (0,1], with existence, uniqueness and the equation as conclusions; reason: the conclusions exclude the default value of an empty or degenerate solution set without adding a hypothesis
--   - encoding: a finite nonempty candidate set with a fixed total order in an arbitrary metric space, positive costs → the published Geometry: an injective enumeration Fin m → M with m > 0 and positive real fees; reason: every finite ordered candidate set has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
--   - encoding: every horizon n, including n = 0 (empty multiset, ALG = OPT = 0) → the upper-bound clauses assume 0 < n; reason: at n = 0 the source's bound reads 0 ≤ 0, while the published optimum minimizes over nonempty facility sets; the hypothesis excludes only this degenerate horizon
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem 1.2 (printed p. 2, PDF p. 4) and Theorem 5.1 (printed p. 16, PDF p. 18); attainment by Corollary 4.11 (printed p. 15, PDF p. 17)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Theorem 1.2 / Theorem 5.1 (PDF pp. 4, 18; printed pp. 2, 16). The root `muD` is certified;
every positive rank-penalty schedule that is `C`-competitive on all finite full-space instances
has `ρ*_D ≤ C`; the shifted schedule at `(µ_D, δ_D)` is in the class and is `ρ*_D`-competitive on
every instance, so the infimum over the class is exactly `ρ*_D`. -/
theorem rank_penalty_optimality :
    (0 < muD ∧ muD ≤ 1 ∧ limitingA muD = balanceG muD ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ 1 → limitingA μ = balanceG μ → μ = muD) ∧
    (∀ lam : ℕ → ℕ → ℝ, IsRankSchedule lam →
      ∀ C : ℝ, FullSpaceCompetitive lam C → rhoD ≤ C) ∧
    IsRankSchedule (fun n t => penalty n t muD deltaD) ∧
    (∀ {M : Type*} [MetricSpace M] (G : Geometry M) {n : ℕ}, 0 < n → ∀ u : Fin n → M,
      uniformAvg (rankPenaltyAlg G u (fun n t => penalty n t muD deltaD)) ≤
        rhoD * optimum G u) := by sorry

end RankCutFacility.Shifted.Supplement
