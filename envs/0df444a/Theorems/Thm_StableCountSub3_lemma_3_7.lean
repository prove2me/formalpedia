-- Prove2me | Theorems.Thm_StableCountSub3_lemma_3_7
-- name    : StableCountSub3.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:50:27.717773+00:00
-- url     : https://prove2.me/theorems/3505d2b6-f18e-4075-8b71-2f44d9aba992
-- title:
--   Lemma 3.7 — candidate bound via cones: $N_m\le1+L_m+R_m$
-- statement:
--   Let $D$ be a downset and $m$ a man, and let $U\in[0,1]^n$ have pairwise distinct coordinates (the probability-one event on which §3 works). Then $N_m(D,U)\le1+L_m(D,U)+R_m(D,U)$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - reading: "We work on the probability-one event that all priorities are distinct" (§3.1, standing assumption of Section 3) → hypotheses U v ∈ [0,1] for all v and Function.Injective U; reason: the standing assumption of the section, stated as a binder; with tied priorities the inequality can fail
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 3.7, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_StableCountSub3_RandomReveal

open StableMatching

namespace StableCountSub3

/-- Lemma 3.7 (candidate bound via cones): `N_m(D, U) ≤ 1 + L_m(D, U) + R_m(D, U)`, for
priorities in `[0, 1]` that are pairwise distinct (the probability-one event of §3.1). -/
theorem lemma_3_7 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (m : Fin n) (U : Fin n → ℝ) (hU : ∀ v, U v ∈ Set.Icc (0 : ℝ) 1)
    (hdist : Function.Injective U) :
    numCand I D m U ≤ 1 + Lm I D m U + Rm I D m U := by sorry

end StableCountSub3
