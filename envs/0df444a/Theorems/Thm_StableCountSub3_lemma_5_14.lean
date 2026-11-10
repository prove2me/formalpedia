-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_14
-- name    : StableCountSub3.lemma_5_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:52:43.540766+00:00
-- url     : https://prove2.me/theorems/7c6644d1-f1af-4a1e-a318-822dcca0a904
-- title:
--   Lemma 5.14 — average basic credit: $g_{\rm basic}=2\delta_1-(\delta_1-\delta_2)e_s\ge\frac23(\delta_1+2\delta_2)$
-- statement:
--   For every instance with $n\ge1$ men, $g_{\rm basic}=2\delta_1-(\delta_1-\delta_2)e_s$ and $g_{\rm basic}\ge\frac23(\delta_1+2\delta_2)$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: averages over (μ, m) uniform on Ω × M with D = D(μ) → avgDm: (1/(|Ω| n)) ∑_{μ ∈ Ω} ∑_m f(D(μ), m), with |Ω| = StableCount.numStable I; reason: the uniform average written out; same value
--   - reading: Lemma 5.14 (no explicit n; M = {m1,…,mn}) → hypothesis 1 ≤ n; reason: the paper works with n ≥ 1 men (Theorem 6.20, p. 42; the paragraph after Theorem 1.1, p. 3); for n = 0 the average over Ω × M is over an empty set and is not defined
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 5.14, p. 31 (PDF 33)

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

/-- Lemma 5.14: `g_basic = 2δ₁ − (δ₁ − δ₂) e_s ≥ (2/3)(δ₁ + 2δ₂)`. -/
theorem lemma_5_14 {n : ℕ} (hn : 1 ≤ n) (I : Instance n) :
    gBasic I = 2 * delta 1 - (delta 1 - delta 2) * es I ∧
    2 / 3 * (delta 1 + 2 * delta 2) ≤ gBasic I := by sorry

end StableCountSub3
