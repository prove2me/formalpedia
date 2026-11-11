-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_expected_high_excess
-- name    : RankCutFacility.Shifted.expected_high_excess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:08.719392+00:00
-- url     : https://prove2.me/theorems/a3b93457-d7e8-4573-88b0-8da87d137e0f
-- title:
--   Lemma 4.9 — Expected high-cost anchor excess
-- statement:
--   Consider Algorithm 1 with $n\ge1$, arbitrary metric geometry, positive opening costs and parameters $\mu,\delta\in(0,1]$. Fix an optimal nearest-assignment solution with no unused facility and a nonempty cluster $C$ at $c$. Put $k=|C|$ and $R(C)=\sum_{u\in C}d(u,c)$. The excess charge $H_p$ is the positive part of the random anchor opening fee minus $f_c$, or zero for no opening. Expectation includes both the random anchor identity and its rank.
--
--   Lemma 4.9. For a cluster of size k, 𝔼[Hₚ] ≤ max{µ/δ, 1/k} R(C).
--
--   This gives both branches of the excess-cost coefficient.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: a fixed optimum with unused facilities removed and its nearest-assignment clusters → Comparator plus IsOptimal and a nonempty assignment fiber; reason: these encode the standing assumptions of Section 4.2, without assuming any online accounting estimate
--   - encoding: uniform or conditional permutation expectation → finite arithmetic averages over all permutations or the indicated nonempty fibers; reason: these are exactly the source finite uniform laws; no integration or measurability assumption is needed
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.9, printed p. 14 (PDF p. 16), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem expected_high_excess {M : Type*} [MetricSpace M] (G : Geometry M)
    {n : ℕ} (hn : 0 < n) (u : Fin n → M) (μ δ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (hC : (cluster Q c).Nonempty) :
    uniformAvg (fun π => anchorAccount (cluster Q c) π (fun p => highOpening G u μ δ c π p)) ≤
      max (μ/δ) (1 / ((cluster Q c).card : ℝ)) * radiusSum G u (cluster Q c) c := by sorry
end RankCutFacility.Shifted
