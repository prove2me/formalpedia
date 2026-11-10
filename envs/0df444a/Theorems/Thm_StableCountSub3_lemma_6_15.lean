-- Prove2me | Theorems.Thm_StableCountSub3_lemma_6_15
-- name    : StableCountSub3.lemma_6_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:52:25.42701+00:00
-- url     : https://prove2.me/theorems/0c9625c9-e89d-4c11-8b27-db9395e4a8b1
-- title:
--   Lemma 6.15 — charging bound on additional credits
-- statement:
--   For every downset $D$ and direction, $\sum_{m\in M}g^\pm_{\rm add}(D,m)\ge t(|B|+|C|)+4t|I|$, where $B,C,I$ are the classes for $D$ and that direction and $t=\delta_4$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 6.15, p. 40 (PDF 42)

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

open Classical in
/-- Lemma 6.15: for a fixed downset and direction,
`∑_{m ∈ M} g^±_add(D, m) ≥ t(|B| + |C|) + 4t|I|`. -/
theorem lemma_6_15 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (dir : Dir) :
    tCredit * (((Finset.univ.filter fun m => InB I D m dir).card : ℝ) +
        ((Finset.univ.filter fun m => InC I D m dir).card : ℝ)) +
      4 * tCredit * ((Finset.univ.filter fun m => InI I D m dir).card : ℝ) ≤
    ∑ m : Fin n, addCredit I D m dir := by sorry

end StableCountSub3
