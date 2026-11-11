-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_expected_anchor_base
-- name    : RankCutFacility.Shifted.expected_anchor_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:14.898654+00:00
-- url     : https://prove2.me/theorems/a1ed48ec-eda4-48d6-ade1-761422cfae72
-- title:
--   Lemma 4.7 — Expected anchor base account
-- statement:
--   Consider the same arbitrary metric instance, Algorithm 1 parameters $\mu,\delta\in(0,1]$, and a nonempty optimal cluster $C$ at $c$. Put $k=|C|$, $f=f_c$, and $r_p=d(p,c)$. For its random anchor $p$, let $L_p$ be the opening fee capped at $f$, or zero if it opens nothing, and let $e_p=(D_p-r_p)^+$. The expectation averages all labeled permutations. Use the all-index coefficient (23):
--
--   $$\Gamma_h=\frac{h^h(h+\delta-\mu)^{h+1}}{\mu(h+\delta)^h(h+1)^{h+1}},\quad A_D=\max\{\delta/\mu,1+\sup_{h\ge1}\Gamma_h\}.$$
--
--   Nonemptiness and boundedness of the set defining that real supremum are also conclusions.
--
--   Lemma 4.7. For every optimal cluster, 𝔼[Lₚ + keₚ] ≤ A_D(µ, δ)f.
--
--   This gives the opening-cost coefficient for the anchor base account.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: a fixed optimum with unused facilities removed and its nearest-assignment clusters → Comparator plus IsOptimal and a nonempty assignment fiber; reason: these encode the standing assumptions of Section 4.2, without assuming any online accounting estimate
--   - encoding: uniform or conditional permutation expectation → finite arithmetic averages over all permutations or the indicated nonempty fibers; reason: these are exactly the source finite uniform laws; no integration or measurability assumption is needed
--   - encoding: the real supremum in (23) or (29) → sSup together with explicit nonemptiness and boundedness conclusions; reason: this excludes the default value of an unbounded real supremum without adding a hypothesis
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.7, printed p. 13 (PDF p. 15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem expected_anchor_base {M : Type*} [MetricSpace M] (G : Geometry M)
    {n : ℕ} (hn : 0 < n) (u : Fin n → M) (μ δ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (hC : (cluster Q c).Nonempty) :
    BddAbove (gammaSet μ δ) ∧ (gammaSet μ δ).Nonempty ∧
    uniformAvg (fun π => anchorAccount (cluster Q c) π (fun p =>
      baseOpening G u μ δ c π p + (cluster Q c).card * excessDistance G u μ δ c π p)) ≤
        openingCoefficient μ δ * G.fee c := by sorry
end RankCutFacility.Shifted
