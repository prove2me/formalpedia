-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_deterministic_bound
-- name    : RankCutFacility.Shifted.deterministic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:07.222054+00:00
-- url     : https://prove2.me/theorems/105670fd-544b-4153-b01e-96196242d6f5
-- title:
--   Theorem 4.10 — Two-coefficient deterministic parameter bound
-- statement:
--   Consider any metric space, finite nonempty candidate set with positive real opening costs, arbitrary $n\ge1$ demand copies (repeated locations allowed), and fixed candidate tie order. Run Algorithm 1 with $\mu,\delta\in(0,1]$ under a uniform labeled permutation. Fix any optimal nearest-assignment solution with no unused facility, with opening cost $F^*$ and connection cost $R^*$. The coefficient $A_D$ uses (23) over all positive integer indices. Its defining set is certified nonempty and bounded above. The function $\rho_D$ denotes the bound supplied by this analysis.
--
--   Theorem 4.10 (Deterministic bound). For µ, δ ∈ (0, 1], Algorithm 1 satisfies
--   $$
--   \mathbb E[\operatorname{ALG}]\le A_D(\mu,\delta)F^*+\left(3+2\mu+\frac\mu\delta\right)R^*.\tag{26}
--   $$
--   Thus, if ρ_D(µ, δ) denotes the competitive-ratio bound supplied by this analysis, then
--   $$
--   \rho_D(\mu,\delta)=\max\left\{A_D(\mu,\delta),3+2\mu+\frac\mu\delta\right\}.
--   $$
--
--   This preserves the separate opening and connection coefficients, as well as their competitive maximum.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: a fixed optimum with unused facilities removed and its nearest-assignment clusters → Comparator plus IsOptimal and a nonempty assignment fiber; reason: these encode the standing assumptions of Section 4.2, without assuming any online accounting estimate
--   - encoding: uniform or conditional permutation expectation → finite arithmetic averages over all permutations or the indicated nonempty fibers; reason: these are exactly the source finite uniform laws; no integration or measurability assumption is needed
--   - encoding: the real supremum in (23) or (29) → sSup together with explicit nonemptiness and boundedness conclusions; reason: this excludes the default value of an unbounded real supremum without adding a hypothesis
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Theorem 4.10, printed p. 15 (PDF p. 17), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem deterministic_bound {M : Type*} [MetricSpace M] (G : Geometry M)
    {n : ℕ} (hn : 0 < n) (u : Fin n → M) (μ δ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) :
    BddAbove (gammaSet μ δ) ∧ (gammaSet μ δ).Nonempty ∧
    uniformAvg (alg G u μ δ) ≤ openingCoefficient μ δ * openingCost G Q.opened +
      (3+2*μ+μ/δ) * connectionCost G u Q.opened ∧
    ratioBound μ δ = max (openingCoefficient μ δ) (3+2*μ+μ/δ) := by sorry
end RankCutFacility.Shifted
