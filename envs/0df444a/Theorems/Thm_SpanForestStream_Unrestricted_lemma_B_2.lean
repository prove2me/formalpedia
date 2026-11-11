-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_B_2
-- name    : SpanForestStream.Unrestricted.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:33.195874+00:00
-- url     : https://prove2.me/theorems/a79c7439-4680-411e-acd3-3ee15ee0c9e4
-- title:
--   Lemma B.2 — insertion-only forest baseline Ω(v log(v + 1))
-- statement:
--   There is an absolute constant $c>0$ such that for every $v\ge 2$, a spanning-forest algorithm on $[v]$ with error at most $1/4$ on every insertion-only legal stream (one report) has, in both peak-space measures,
--   $$s+1\ge c\,v\log_2(v+1).$$
--
--   This covers the bounded-budget cases of Corollary 4.9.
--
--   Differences from the source:
--   - encoding: Ω(v log(v + 1)) bits for both peak-space measures → ∃ absolute c > 0 with c·v·log₂(v+1) ≤ expPeak + 1 and ≤ hardPeak + 1; reason: O/Ω as absolute constants; App. A: space is peak + 1
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 52 (PDF 55), Lemma B.2

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Lemma B.2 (insertion-only forest baseline): there is an absolute `c > 0` such that for every
`v ≥ 2`, every algorithm with error at most `1/4` on insertion-only legal streams has
`s + 1 ≥ c v log₂(v + 1)` in both peak-space measures. -/
theorem lemma_B_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ v : ℕ, 2 ≤ v → ∀ A : Transducer v,
      (∀ w : List (Update v), IsLegal w → IsInsertionOnly w → A.errorProb w ≤ 1 / 4) →
      ENNReal.ofReal (c * v * Real.logb 2 (v + 1)) ≤ A.expPeak + 1 ∧
      ENNReal.ofReal (c * v * Real.logb 2 (v + 1)) ≤ A.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
