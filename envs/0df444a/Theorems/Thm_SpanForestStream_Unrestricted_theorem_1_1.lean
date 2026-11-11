-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_theorem_1_1
-- name    : SpanForestStream.Unrestricted.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:22.094229+00:00
-- url     : https://prove2.me/theorems/06b2d74e-533e-446d-a693-a49af8b0db0a
-- title:
--   Theorem 1.1 — space lower bound Ω(min{v², v log(v/δ) log²(2 + v/log(v/δ))}) at every confidence level
-- statement:
--   There is an absolute constant $c>0$ such that for every $v\ge 2$ and every $0<\delta\le 1/4$, every algorithm that recovers a spanning forest with one report and failure probability at most $\delta$ on every legal dynamic stream of simple graphs on $[v]$ has, in both peak-space measures,
--   $$s+1\ge c\,f(v,\delta),\qquad f(v,\delta)=\min\Big\{v^2,\ v\log_2(v/\delta)\log_2^2\Big(2+\frac{v}{\log_2(v/\delta)}\Big)\Big\}.$$
--   The lower bound applies to arbitrary algorithms, including nonlinear algorithms, and to every $\delta\in(0,1/4]$, including $\delta$ far below $2^{-v}$.
--
--   Differences from the source:
--   - reading: App. A's algorithm: an event-driven private-randomness transducer whose total peak memory (setup data, stored randomness, retained state, update and decoding scratch, output buffers) is charged → `Transducer v`: bit-string complete states, a setup law, one Markov kernel per update symbol with a non-termination outcome, a report kernel reading the final state with fresh coins; peak = largest state length at the event boundaries; reason: App. A fixes no finer machine; with arbitrary transitions, scratch inside one event is not visible at the boundaries (the separately stated running-time and workspace guarantees of §1.5 are outside Theorems 1.1/1.2)
--   - encoding: 'requires, in bits, Ω(·)'; the constants are absolute → ∃ c > 0 before v and δ with c·f(v, δ) ≤ expPeak + 1 and ≤ hardPeak + 1; reason: App. A: space is peak + 1, Ω with an absolute constant; the two measures are those of §1.5
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 3 (PDF 6), Theorem 1.1

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer
import Definitions.Def_SpanForestStream_Unrestricted_SpaceFunction

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Theorem 1.1 (space lower bound at every confidence level): there is an absolute `c > 0` such
that for every `v ≥ 2` and `0 < δ ≤ 1/4`, every algorithm (linear or not) recovering a spanning
forest at one report with failure probability at most `δ` on every legal dynamic stream on `[v]`
has `s + 1 ≥ c f(v, δ)` in both peak-space measures, where
`f(v, δ) = min{v², v log₂(v/δ) log₂²(2 + v/log₂(v/δ))}`. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : ℕ) (δ : ℝ), 2 ≤ v → 0 < δ → δ ≤ 1 / 4 →
      ∀ A : Transducer v,
        (∀ w : List (Update v), IsLegal w → A.errorProb w ≤ ENNReal.ofReal δ) →
        ENNReal.ofReal (c * spaceFn v δ) ≤ A.expPeak + 1 ∧
        ENNReal.ofReal (c * spaceFn v δ) ≤ A.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
