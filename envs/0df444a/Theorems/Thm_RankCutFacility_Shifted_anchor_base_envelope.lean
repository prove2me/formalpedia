-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_anchor_base_envelope
-- name    : RankCutFacility.Shifted.anchor_base_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:21.207706+00:00
-- url     : https://prove2.me/theorems/bb1172ff-4785-4103-9833-da7ef8c08818
-- title:
--   Lemma 4.6 — Anchor base opening plus inherited connection distance
-- statement:
--   Consider Algorithm 1 with $n\ge1$, positive opening costs and $\mu,\delta\in(0,1]$, and a fixed optimal nearest-assignment solution with no unused facility. Let $C$ be a nonempty cluster at $c$, $k=|C|$, $f=f_c$, and $r_p=d(p,c)$. Fix an anchor identity $p\in C$ and an attainable relative order of the labels outside $C$. If $p$ opens $y$, let $L_p=\min(f_y,f)$, otherwise $L_p=0$; set $e_p=(D_p-r_p)^+$. The witness below precedes the universal quantifier over every compatible permutation.
--
--   Lemma 4.6. Fix p and the relative order of the requests outside C. There are finitely many nonnegative weights wᵢ and thresholds xᵢ ∈ [0, 1], independent of the first rank T, with ∑ᵢ wᵢ = f, such that
--   $$
--   L_p+ke_p\le\sum_iw_i\bigl[1+(kx_i-1)^+\mathbf1\{q_T\ge\mu x_i\}\bigr].\tag{20}
--   $$
--
--   The same list covers opening and nonopening outcomes and cannot depend on the realized first rank.
--
--   Differences from the source:
--   - encoding: a finite ordered candidate set in an arbitrary metric space → an injective enumeration by Fin m with m > 0, with its usual order; reason: every finite candidate set and fixed total order has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n request copies → an arbitrary map Fin n → M with n > 0; reason: labels distinguish repeated copies for permutations and never enter an online decision
--   - encoding: a fixed optimum with unused facilities removed and its nearest-assignment clusters → Comparator plus IsOptimal and a nonempty assignment fiber; reason: these encode the standing assumptions of Section 4.2, without assuming any online accounting estimate
--   - encoding: finite switching lists and inclusive indices 1 through m → functions on Fin m or edge indices 0 through m-1; reason: this reindexes every summand and retains the empty-list case and non-strict switch tests
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.6, printed p. 12 (PDF p. 14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem anchor_base_envelope {M : Type*} [MetricSpace M] (G : Geometry M)
    {n : ℕ} (hn : 0 < n) (u : Fin n → M) (μ δ : ℝ)
    (hμ : 0 < μ ∧ μ ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1)
    (Q : Comparator G n) (hQ : IsOptimal G u Q) (c : Fin G.m)
    (hC : (cluster Q c).Nonempty)
    (p : Fin n) (hp : p ∈ cluster Q c) (o : List (Fin n))
    (ho : (identityOutsideFiber (cluster Q c) p o).Nonempty) :
    ∃ m : ℕ, ∃ w x : Fin m → ℝ,
      (∀ i, 0 ≤ w i ∧ 0 ≤ x i ∧ x i ≤ 1) ∧ (∑ i, w i) = G.fee c ∧
      ∀ π ∈ identityOutsideFiber (cluster Q c) p o,
        baseOpening G u μ δ c π p + (cluster Q c).card * excessDistance G u μ δ c π p ≤
          ∑ i, w i * (1 + if μ*x i ≤ clock n (rank π p) δ then
            positivePart ((cluster Q c).card * x i - 1) else 0) := by sorry
end RankCutFacility.Shifted
