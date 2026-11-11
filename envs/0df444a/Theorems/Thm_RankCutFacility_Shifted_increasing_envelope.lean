-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_increasing_envelope
-- name    : RankCutFacility.Shifted.increasing_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:58.135865+00:00
-- url     : https://prove2.me/theorems/0c728131-b17d-41c0-935b-9c82613a4341
-- title:
--   Lemma 4.2 — Increasing envelope and fractional switch portions (corrected: nonnegative empty-family budget)
-- statement:
--   Let $\mathcal P$ be a finite set of lines $ta-b$, with $0\le a\le A$ and $b\ge0$. Take $A\ge0$, including when the family is empty. Set $V(t)=\max(\{0\}\cup\{ta-b:(a,b)\in\mathcal P\})$ for $t\ge0$. A single finite switching list must work at every time and for every maximizing line.
--
--   Lemma 4.2. Consider a finite family of lines taⱼ − bⱼ with slopes 0 ≤ aⱼ ≤ A and offsets bⱼ ≥ 0. Let V(t) = max({0} ∪ {taⱼ − bⱼ : j}) be their nonnegative upper envelope for t ≥ 0. There are finitely many positive weights wᵢ and thresholds xᵢ ≥ 0 such that
--   $$
--   V(t)=\sum_iw_i(t-x_i)^+,\qquad\sum_iw_i\le A.\tag{10}
--   $$
--   If ta − b is a maximizing line at t > 0, there are portions sᵢ of the switching weights, with 0 ≤ sᵢ ≤ wᵢ and sᵢ = 0 whenever xᵢ > t, such that
--   $$
--   \sum_i s_i=a,\qquad\sum_i s_ix_i=b.\tag{11}
--   $$
--
--   This supplies both a slope budget and the first-moment portions needed at a switching tie.
--
--   Differences from the source:
--   - correction: a finite family with 0 ≤ a_j ≤ A, allowing an empty family without requiring A ≥ 0 → also require 0 ≤ A; reason: for the empty family and A = -1 all printed hypotheses hold, while (10) requires a nonnegative sum of positive weights to be at most -1; nonempty families already imply A ≥ 0
--   - encoding: finite switching lists and inclusive indices 1 through m → functions on Fin m or edge indices 0 through m-1; reason: this reindexes every summand and retains the empty-list case and non-strict switch tests
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.2, printed p. 10 (PDF p. 12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
/-- Corrected only for the empty family: the slope budget A must be nonnegative.
For P = ∅ and A = -1 the printed hypotheses are vacuous, but (10) would say
that a sum of positive weights is at most -1. -/
theorem increasing_envelope (P : Finset (ℝ × ℝ)) (A : ℝ) (hA : 0 ≤ A)
    (hP : ∀ v ∈ P, 0 ≤ v.1 ∧ v.1 ≤ A ∧ 0 ≤ v.2) :
    ∃ m : ℕ, ∃ w x : Fin m → ℝ,
      (∀ i, 0 < w i ∧ 0 ≤ x i) ∧
      (∀ t : ℝ, 0 ≤ t → increasingEnvelope P t = ∑ i, w i * positivePart (t-x i)) ∧
      (∑ i, w i) ≤ A ∧
      (∀ v ∈ P, ∀ t : ℝ, 0 < t → t*v.1-v.2 = increasingEnvelope P t →
        ∃ s : Fin m → ℝ, (∀ i, 0 ≤ s i ∧ s i ≤ w i ∧ (t < x i → s i = 0)) ∧
          (∑ i, s i) = v.1 ∧ (∑ i, s i*x i) = v.2) := by sorry
end RankCutFacility.Shifted
