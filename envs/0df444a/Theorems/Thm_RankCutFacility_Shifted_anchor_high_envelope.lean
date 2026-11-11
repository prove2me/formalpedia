-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_anchor_high_envelope
-- name    : RankCutFacility.Shifted.anchor_high_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:12.577198+00:00
-- url     : https://prove2.me/theorems/7ebab416-89a6-46c7-a2da-51aca60ebe72
-- title:
--   Lemma 4.8 — High-cost anchor excess as a fixed finite envelope
-- statement:
--   Consider Algorithm 1 with arbitrary metric geometry, positive opening costs, $n\ge1$ and $\mu,\delta\in(0,1]$. Fix an optimal solution with no unused facility, a nonempty cluster $C$ at $c$, and an anchor label $p\in C$. Put $f=f_c$ and $r_p=d(p,c)$. If $p$ opens $y$, let $H_p=(f_y-f)^+$, otherwise $H_p=0$. One finite witness must work for every arrival permutation with that anchor, before any rank or outside history is specified.
--
--   Lemma 4.8. For each fixed anchor identity p, there is a finite list of positive weights wᵢ and nonnegative thresholds xᵢ, depending only on p and the instance, such that
--   $$
--   H_p\le\sum_iw_i\mathbf1\{\alpha\le x_i\},\qquad\sum_iw_ix_i\le r_p.\tag{24}
--   $$
--
--   This bounds expensive openings and their first moment uniformly over all histories.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: a fixed optimum with unused facilities removed and its nearest-assignment clusters → Comparator plus IsOptimal and a nonempty assignment fiber; reason: these encode the standing assumptions of Section 4.2, without assuming any online accounting estimate
--   - encoding: finite switching lists and inclusive indices 1 through m → functions on Fin m or edge indices 0 through m-1; reason: this reindexes every summand and retains the empty-list case and non-strict switch tests
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.8, printed p. 14 (PDF p. 16), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
/-- The witness depends only on the instance, comparator cluster, and anchor label.
It precedes all schedule parameters, arrival ranks, and outside histories. -/
theorem anchor_high_envelope {M : Type*} [MetricSpace M] (G : Geometry M)
    {n : ℕ} (hn : 0 < n) (u : Fin n → M)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (hC : (cluster Q c).Nonempty) (p : Fin n) (hp : p ∈ cluster Q c) :
    ∃ m : ℕ, ∃ w x : Fin m → ℝ,
      (∀ i, 0 < w i ∧ 0 ≤ x i) ∧
      (∑ i, w i*x i) ≤ dist (u p) (G.site c) ∧
      ∀ μ δ : ℝ, 0 < μ ∧ μ ≤ 1 → 0 < δ ∧ δ ≤ 1 →
        ∀ π : Arrival n, anchor (cluster Q c) π = some p →
          highOpening G u μ δ c π p ≤
            ∑ i, if penalty n (rank π p) μ δ ≤ x i then w i else 0 := by sorry
end RankCutFacility.Shifted
