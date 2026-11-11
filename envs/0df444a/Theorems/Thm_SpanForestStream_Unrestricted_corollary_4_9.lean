-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_corollary_4_9
-- name    : SpanForestStream.Unrestricted.corollary_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:26.235199+00:00
-- url     : https://prove2.me/theorems/3d859462-1bdd-453a-a8ae-a5bf3383dfe1
-- title:
--   Corollary 4.9 — constant-error lower bound Ω(v log(v+1) min{log²(Z+2), log²(v+1)})
-- statement:
--   There is an absolute constant $c>0$ such that for all $v\ge 2$ and integers $Z\ge 0$, every algorithm returning a spanning forest with error at most $1/4$ on every fixed legal stream with at most $Z$ deletion operations (one report) has, in both peak-space measures,
--   $$s+1\ge c\,v\log_2(v+1)\,\min\{\log_2^2(Z+2),\ \log_2^2(v+1)\}.\qquad(4.22)$$
--
--   With $Z\ge\binom v2$ there is no effective deletion restriction, and this is the $\Omega(vA^3)$ baseline that Proposition 3.6 needs.
--
--   Differences from the source:
--   - reading: 'The algorithm in Theorem 4.13 uses space matching this lower bound on simple graphs.' → not stated; reason: a cross-reference to Theorem 4.13, a separately stated result outside this mission (README); the corollary's own claim is the lower bound
--   - encoding: Ω(·) bits, both peak-space measures → ∃ absolute c > 0, bounds on expPeak + 1 and hardPeak + 1; reason: App. A: space is peak + 1
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 33 (PDF 36), Corollary 4.9, Eq. (4.22)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Corollary 4.9 (matching constant-error lower bound on the bounded-deletion subclass): there is
an absolute `c > 0` such that for all `v ≥ 2` and `Z ≥ 0`, every algorithm with error at most
`1/4` on every legal stream with at most `Z` deletion operations has, in both peak-space measures,
`s + 1 ≥ c v log₂(v+1) min{log₂²(Z+2), log₂²(v+1)}`. -/
theorem corollary_4_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ (v Z : ℕ), 2 ≤ v → ∀ A : Transducer v,
      (∀ w : List (Update v), IsLegal w → numDeletions w ≤ Z → A.errorProb w ≤ 1 / 4) →
      ENNReal.ofReal (c * v * Real.logb 2 (v + 1) *
          min (Real.logb 2 (Z + 2) ^ 2) (Real.logb 2 (v + 1) ^ 2)) ≤ A.expPeak + 1 ∧
      ENNReal.ofReal (c * v * Real.logb 2 (v + 1) *
          min (Real.logb 2 (Z + 2) ^ 2) (Real.logb 2 (v + 1) ^ 2)) ≤ A.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
