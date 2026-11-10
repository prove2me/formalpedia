-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_11
-- name    : StableCountSub3.lemma_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:52:12.87312+00:00
-- url     : https://prove2.me/theorems/a09fbd62-fac9-4822-a498-f6e1c0e56610
-- title:
--   Lemma 5.11 — bijections between pointed matchings
-- statement:
--   Among pointed matchings $(D,m)$ ($D$ a downset, $m$ a man), there is a bijection between those simple in both directions and those with $m\in C$ in the backward direction, and a bijection between those simple in both directions and those with $m\in C$ in the forward direction.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: "There is a bijection between pointed matchings …" → Nonempty (Equiv) between the two subtypes of Finset (Rot n) × Fin n; reason: existence of a bijection between finite sets
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 5.11, p. 29 (PDF 31)

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

/-- Lemma 5.11: bijections between the pointed matchings `(D, m)` simple in both directions and
those with `m ∈ C` backward, and likewise forward. -/
theorem lemma_5_11 {n : ℕ} (I : Instance n) :
    Nonempty ({p : Finset (Rot n) × Fin n //
        IsDownset I p.1 ∧ IsSimple I p.1 p.2 .bwd ∧ IsSimple I p.1 p.2 .fwd} ≃
      {p : Finset (Rot n) × Fin n // IsDownset I p.1 ∧ InC I p.1 p.2 .bwd}) ∧
    Nonempty ({p : Finset (Rot n) × Fin n //
        IsDownset I p.1 ∧ IsSimple I p.1 p.2 .bwd ∧ IsSimple I p.1 p.2 .fwd} ≃
      {p : Finset (Rot n) × Fin n // IsDownset I p.1 ∧ InC I p.1 p.2 .fwd}) := by sorry

end StableCountSub3
