-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_decreasing_envelope
-- name    : RankCutFacility.Shifted.decreasing_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:57.282291+00:00
-- url     : https://prove2.me/theorems/5ca76958-b29f-4133-96d0-b7c3460e135d
-- title:
--   Lemma 4.1 — Decreasing cost–benefit envelope, including switch ties
-- statement:
--   Let $\mathcal P$ be a finite set of real cost–benefit pairs containing the origin. Both coordinates are nonnegative and every nonorigin pair has positive cost. Retain precisely the pairs maximizing $b-ta$ at some $t>0$ and sort them by cost. Edges below use zero-based indices in Lean.
--
--   Lemma 4.1. Let 𝒫 be a finite set of cost–benefit pairs (a, b) with nonnegative coordinates, containing the origin, and with a > 0 at every nonorigin point. The linear objective b − ta discounts benefit by a penalty t on cost. Retain all pairs that maximize this objective for some t > 0, and list them in increasing cost coordinate as v₀ = (0, 0), v₁ = (a₁, b₁), . . . , vₘ = (aₘ, bₘ). For the step from vᵢ₋₁ to vᵢ, let wᵢ = aᵢ − aᵢ₋₁ be the cost increment and gᵢ = bᵢ − bᵢ₋₁ the benefit increment. Let xᵢ = gᵢ/wᵢ be the switching penalty at which the two endpoints tie. Then wᵢ > 0, gᵢ ≥ 0, and x₁ ≥ · · · ≥ xₘ. If a retained point vℓ maximizes at t > 0, then
--   $$
--   a_\ell=\sum_{i\le\ell}w_i,\quad b_\ell=\sum_{i\le\ell}w_ix_i,\quad x_i\ge t\ (i\le\ell),\quad x_i\le t\ (i>\ell).\tag{8}
--   $$
--   Consequently, for every t ≥ 0,
--   $$
--   \max_{(a,b)\in\mathcal P}(b-ta)=\sum_{i=1}^m w_i(x_i-t)^+,\qquad\sum_{i=1}^m w_ix_i=\max_{(a,b)\in\mathcal P}b.\tag{9}
--   $$
--   The assertions hold for every maximizing retained point, regardless of the fixed tie-breaking.
--
--   This identifies cost increments, first moments and all switch ties for finite candidate comparisons.
--
--   Differences from the source:
--   - encoding: finite switching lists and inclusive indices 1 through m → functions on Fin m or edge indices 0 through m-1; reason: this reindexes every summand and retains the empty-list case and non-strict switch tests
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.1, printed p. 9 (PDF p. 11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem decreasing_envelope (P : Finset (ℝ × ℝ)) (h0 : (0,0) ∈ P)
    (hpos : ∀ v ∈ P, 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ (v ≠ (0,0) → 0 < v.1)) :
    vertex P 0 = (0,0) ∧
    (∀ i < edgeCount P, 0 < weight P i ∧ 0 ≤ benefit P i) ∧
    (∀ i j : ℕ, i ≤ j → j < edgeCount P → switch P j ≤ switch P i) ∧
    (∀ ℓ < (vertices P).length, ∀ t : ℝ, 0 < t →
      (∀ v ∈ P, v.2-t*v.1 ≤ (vertex P ℓ).2-t*(vertex P ℓ).1) →
      (vertex P ℓ).1 = ∑ i ∈ Finset.range ℓ, weight P i ∧
      (vertex P ℓ).2 = ∑ i ∈ Finset.range ℓ, weight P i * switch P i ∧
      (∀ i < ℓ, t ≤ switch P i) ∧
      (∀ i : ℕ, ℓ ≤ i → i < edgeCount P → switch P i ≤ t)) ∧
    (∀ t : ℝ, 0 ≤ t → decreasingEnvelope P t =
      ∑ i ∈ Finset.range (edgeCount P), weight P i * positivePart (switch P i - t)) ∧
    (∑ i ∈ Finset.range (edgeCount P), weight P i * switch P i) = decreasingEnvelope P 0 := by sorry
end RankCutFacility.Shifted
