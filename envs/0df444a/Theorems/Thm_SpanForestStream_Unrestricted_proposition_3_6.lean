-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_proposition_3_6
-- name    : SpanForestStream.Unrestricted.proposition_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:28.674182+00:00
-- url     : https://prove2.me/theorems/7a56209c-1a7d-4d07-be91-9f956f2e4cfe
-- title:
--   Proposition 3.6 — s + 1 = Ω(min{v², v(A + t) log²(2 + v/(A + t))}) in both measures
-- statement:
--   There is an absolute constant $c>0$ such that, for spanning-forest output on fixed legal dynamic graph streams with no deletion or length promise, with $v\ge 2$, $0<\delta\le 1/4$, $A=\lceil\log_2(v+1)\rceil$ and $t=1+\log_2(1/\delta)$: every algorithm with failure probability at most $\delta$ on every legal stream has, for $s$ its worst-case or its worst-input expected peak space,
--   $$s+1\ge c\,\min\Big\{v^2,\ v(A+t)\log_2^2\Big(2+\frac{v}{A+t}\Big)\Big\}.\qquad(3.21)$$
--
--   Differences from the source:
--   - reading: App. A's algorithm: an event-driven private-randomness transducer whose total peak memory (setup data, stored randomness, retained state, update and decoding scratch, output buffers) is charged → `Transducer v`: bit-string complete states, a setup law, one Markov kernel per update symbol with a non-termination outcome, a report kernel reading the final state with fresh coins; peak = largest state length at the event boundaries; reason: App. A fixes no finer machine; with arbitrary transitions, scratch inside one event is not visible at the boundaries (the separately stated running-time and workspace guarantees of §1.5 are outside Theorems 1.1/1.2)
--   - encoding: Ω(·), s + 1 → ∃ absolute c > 0 before v and δ; bounds on expPeak + 1 and hardPeak + 1; reason: App. A: space is peak + 1
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 21 (PDF 24), Proposition 3.6, Eq. (3.21)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer
import Definitions.Def_SpanForestStream_Unrestricted_SpaceFunction

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Proposition 3.6 (matching space lower bound at every confidence level): there is an absolute
`c > 0` such that for `v ≥ 2`, `0 < δ ≤ 1/4`, `A = ⌈log₂(v+1)⌉` and `t = 1 + log₂(1/δ)`, every
algorithm with failure probability at most `δ` on every legal stream has, in both peak-space
measures, `s + 1 ≥ c min{v², v(A + t) log₂²(2 + v/(A + t))}`. -/
theorem proposition_3_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : ℕ) (δ : ℝ), 2 ≤ v → 0 < δ → δ ≤ 1 / 4 →
      ∀ A : Transducer v,
        (∀ w : List (Update v), IsLegal w → A.errorProb w ≤ ENNReal.ofReal δ) →
        ENNReal.ofReal (c * min ((v : ℝ) ^ 2) (v * ((ceilLog v : ℝ) + confT δ) *
            Real.logb 2 (2 + v / ((ceilLog v : ℝ) + confT δ)) ^ 2)) ≤ A.expPeak + 1 ∧
        ENNReal.ofReal (c * min ((v : ℝ) ^ 2) (v * ((ceilLog v : ℝ) + confT δ) *
            Real.logb 2 (2 + v / ((ceilLog v : ℝ) + confT δ)) ^ 2)) ≤ A.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
