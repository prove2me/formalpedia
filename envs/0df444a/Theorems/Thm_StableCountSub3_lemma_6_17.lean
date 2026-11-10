-- Prove2me | Theorems.Thm_StableCountSub3_lemma_6_17
-- name    : StableCountSub3.lemma_6_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:52:06.324285+00:00
-- url     : https://prove2.me/theorems/b6461410-9bfc-43f1-9385-4cc3fe793674
-- title:
--   Lemma 6.17 — $\log|\Omega|\le n(C_0-g_{\rm basic}-g_{\rm add})$
-- statement:
--   For every instance with $n$ men, $\log|\Omega|\le n\,(C_0-g_{\rm basic}-g_{\rm add})$.
--
--   Differences from the source:
--   - encoding: men M = {m1,…,mn}, women W = {w1,…,wn}, strict complete preference lists, perfect matchings as bijections M → W, the order ⪯ and the cover relation ⋖ of Definitions 2.3 and 2.5 → the published StableMatching.Instance n (men and women both Fin n, preferences as rank bijections, rank 0 = most preferred), Matching n = Fin n ≃ Fin n, StableCount.MatchingLE / StableCount.Covers; reason: the same objects: a rank bijection is a strict total order, and MatchingLE/Covers are Definitions 2.3 and 2.5 word for word
--   - encoding: s^±_{m,D}(k) = ∞ and undefined cones/supports when the k-th rotation does not exist → ssize : ℕ∞ with ⊤ for ∞; principalCone and supp are Option-valued (none = undefined); reason: Lean convention; comparisons such as s ≥ d+2 are true at ⊤, as the paper uses them
--   - encoding: averages over (μ, m) uniform on Ω × M with D = D(μ) → avgDm: (1/(|Ω| n)) ∑_{μ ∈ Ω} ∑_m f(D(μ), m), with |Ω| = StableCount.numStable I; reason: the uniform average written out; same value
--   - generalization: uniform averages on pointed matchings Ω × M, requiring n ≥ 1 → also n = 0, with gBasic I = gAdd I = 0 by the totalized finite-average definition; reason: for n ≥ 1 this is exactly the source; at n = 0 there is one empty stable matching and the inequality reduces to log 1 ≤ 0
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604 (held copy, sha256 3caa9340…), Lemma 6.17, p. 41 (PDF 43)

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

/-- Lemma 6.17: `log |Ω| ≤ n (C₀ − g_basic − g_add)`. -/
theorem lemma_6_17 {n : ℕ} (I : Instance n) :
    Real.log (StableCount.numStable I : ℝ) ≤ n * (C0 - gBasic I - gAdd I) := by sorry

end StableCountSub3
