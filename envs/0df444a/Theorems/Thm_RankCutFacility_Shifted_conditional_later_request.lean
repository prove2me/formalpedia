-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_conditional_later_request
-- name    : RankCutFacility.Shifted.conditional_later_request
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:01.987248+00:00
-- url     : https://prove2.me/theorems/446687cc-5e64-4ef0-8f5d-ec1271b9c7b0
-- title:
--   Lemma 4.5 — Conditional later-request estimate with signed correction
-- statement:
--   Consider Algorithm 1 on an arbitrary metric instance with $n\ge1$, positive opening costs and $\mu,\delta\in(0,1]$. Fix an optimal nearest-assignment solution with no unused open facility, a nonempty cluster $C$ served by $c$, and an arrival permutation whose first cluster copy is $p$. Let $\alpha=\lambda_{\operatorname{rank}(p)}$ and $D_p$ be its post-service connection distance. For every fixed different label $u\in C$, average its actual opening-plus-service charge over the permutations sharing the ordered prefix through $p$.
--
--   Lemma 4.5. For each fixed u ∈ C ∖ {p},
--   $$
--   \mathbb E[\operatorname{ALG}(u)\mid\mathcal G_p]\le D_p+d(p,u)+\mu\bigl(\phi_\alpha(p)+d(p,u)-\phi_\alpha(u)\bigr).\tag{15}
--   $$
--
--   The signed correction is retained for subsequent cluster accounting; no conditional anchor symmetry is assumed.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: a fixed optimum with unused facilities removed and its nearest-assignment clusters → Comparator plus IsOptimal and a nonempty assignment fiber; reason: these encode the standing assumptions of Section 4.2, without assuming any online accounting estimate
--   - encoding: uniform or conditional permutation expectation → finite arithmetic averages over all permutations or the indicated nonempty fibers; reason: these are exactly the source finite uniform laws; no integration or measurability assumption is needed
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.5, printed p. 11 (PDF p. 13), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem conditional_later_request {M : Type*} [MetricSpace M] (G : Geometry M)
    {n : ℕ} (hn : 0 < n) (u : Fin n → M) (μ δ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (hC : (cluster Q c).Nonempty)
    (π : Arrival n) (p a : Fin n) (hp : anchor (cluster Q c) π = some p)
    (ha : a ∈ cluster Q c) (hne : a ≠ p) :
    avg (prefixFiber (cluster Q c) π) (fun σ => copyCost G u μ δ σ a) ≤
      copyDistance G u μ δ π p + dist (u p) (u a) +
      μ * (phi G (penalty n (rank π p) μ δ) (u p) + dist (u p) (u a) -
        phi G (penalty n (rank π p) μ δ) (u a)) := by sorry
end RankCutFacility.Shifted
