-- Prove2me | Theorems.Thm_StableCountSub3_theorem_1_1
-- name    : StableCountSub3.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:47:47.472848+00:00
-- url     : https://prove2.me/theorems/0c30ade1-4fe6-4e68-9cb4-4f34b3743b9d
-- title:
--   Theorem 1.1 — fewer than $2.999^n$ stable matchings
-- statement:
--   For every $n\ge1$, every stable matching instance with $n$ men and $n$ women (strict, complete preference lists) has strictly fewer than $2.999^n$ stable matchings: $|\Omega|<2.999^n$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - reading: Theorem 1.1: "Every stable matching instance with n men and n women admits fewer than 2.999^n stable matchings" (no n ≥ 1) → ∀ n, 1 ≤ n → …; reason: the next paragraph says "The theorem holds for every n ≥ 1" and the restatement Theorem 6.20 assumes n ≥ 1; at n = 0 the strict bound fails (1 < 1), an obvious omission (INSIGHTS I1)
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Theorem 1.1, p. 3 (PDF 5)

import Mathlib
import Definitions.Def_StableMatching_GaleShapley
import Definitions.Def_StableCount_Count

namespace StableCountSub3

/-- Theorem 1.1 (= Theorem 6.20): every stable matching instance with `n ≥ 1` men and `n` women
has fewer than `2.999ⁿ` stable matchings. -/
theorem theorem_1_1 : ∀ n : ℕ, 1 ≤ n → ∀ I : StableMatching.Instance n,
    (StableCount.numStable I : ℝ) < (2.999 : ℝ) ^ n := by sorry

end StableCountSub3
