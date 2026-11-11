-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_theorem_1_2
-- name    : SpanForestStream.Unrestricted.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:32.856817+00:00
-- url     : https://prove2.me/theorems/aa544b43-8a08-4ea5-b96f-78955a9c1665
-- title:
--   Theorem 1.2 — space-optimal fully dynamic algorithm: F₂-linear sketch in Θ(min{v², v log(v/δ) log²(2 + v/log(v/δ))}) bits
-- statement:
--   There are absolute constants $C,c>0$ such that for every $v\ge 2$ and every $0<\delta\le 1/4$, with
--   $$f(v,\delta)=\min\Big\{v^2,\ v\log_2(v/\delta)\,\log_2^2\Big(2+\frac{v}{\log_2(v/\delta)}\Big)\Big\}:$$
--
--   (a)–(c) some one-pass randomized algorithm on $[v]$ satisfies all of the following.
--   - Its worst-case peak space satisfies $s+1\le C\,f(v,\delta)$ on every random tape and every legal stream, which bounds the expected measure too.
--   - It recovers a spanning forest at the one report with failure probability at most $\delta$ on every fixed legal dynamic stream (unrestricted deletions).
--   - Conditional on its stored setup it maintains a binary linear sketch over $\mathbb F_2$: its whole persistent state at every event boundary is a canonical encoding of $(\rho,M_\rho x)$, with $\rho$ graph-independent setup data drawn once and $M_\rho$ $\mathbb F_2$-linear in the current adjacency vector $x$.
--
--   (d) It matches Theorem 1.1 and is therefore space-optimal: every algorithm with failure probability at most $\delta$ on every legal stream has $s+1\ge c\,f(v,\delta)$ in both peak-space measures.
--
--   The two halves determine the optimal space at every confidence level $\delta\in(0,1/4]$, including the high-confidence range where the earlier bounds did not meet.
--
--   Differences from the source:
--   - reading: App. A's algorithm: an event-driven private-randomness transducer whose total peak memory (setup data, stored randomness, retained state, update and decoding scratch, output buffers) is charged → `Transducer v`: bit-string complete states, a setup law, one Markov kernel per update symbol with a non-termination outcome, a report kernel reading the final state with fresh coins; peak = largest state length at the event boundaries; reason: App. A fixes no finer machine; with arbitrary transitions, scratch inside one event is not visible at the boundaries (the separately stated running-time and workspace guarantees of §1.5 are outside Theorems 1.1/1.2)
--   - reading: 'the one-pass algorithm' (uniform, reads v and δ at setup) → for every v and δ some transducer on [v] (an algorithm family indexed by the parameters it reads at setup); reason: Lemma 3.2 and App. A supply v, δ at setup; uniformity is part of the separately stated running-time guarantees
--   - encoding: 'using, in bits, O(…)'; 'It matches Theorem 1.1 and is therefore space-optimal'; the constants are absolute → ∃ C, c > 0 before v and δ; hardPeak + 1 ≤ C·f(v, δ) for the algorithm, and c·f(v, δ) ≤ expPeak + 1 and ≤ hardPeak + 1 for every algorithm with failure ≤ δ; reason: App. A: space is peak + 1; the expected measure is at most the worst-case one
--   - encoding: 'Conditional on its stored setup, the algorithm maintains a binary linear sketch over F2' → `IsRetainedLinear`: ∃ a setup law on ρ, s, F₂-linear M_ρ and an injective encoding with run = law of (enc(ρ, M_ρ x_{w_0}), …, enc(ρ, M_ρ x_{w})) under one ρ, every update finishing; reason: the retained-linear state of §6.1, stated pathwise along the run, with one dimension s for every ρ (Prop. 3.3 — the dimension can be fixed by zero padding); its effectiveness remark (computable columns) is not encoded
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 3 (PDF 6), Theorem 1.2, Eq. (1.1)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer
import Definitions.Def_SpanForestStream_Unrestricted_SpaceFunction

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Theorem 1.2 (space-optimal fully dynamic algorithm): there are absolute `C, c > 0` such that for
every `v ≥ 2` and `0 < δ ≤ 1/4`:
(a)–(c) some algorithm has worst-case peak space `s + 1 ≤ C f(v, δ)`, failure probability at most
`δ` on every legal dynamic stream, and, conditional on its setup, a binary linear sketch over `F₂` of
the current adjacency vector as its whole persistent state;
(d) it matches Theorem 1.1: every algorithm with failure probability at most `δ` on every legal
stream has `s + 1 ≥ c f(v, δ)` in both peak-space measures. -/
theorem theorem_1_2 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (v : ℕ) (δ : ℝ), 2 ≤ v → 0 < δ → δ ≤ 1 / 4 →
      (∃ A : Transducer v,
        A.hardPeak + 1 ≤ ENNReal.ofReal (C * spaceFn v δ) ∧
        (∀ w : List (Update v), IsLegal w → A.errorProb w ≤ ENNReal.ofReal δ) ∧
        A.IsRetainedLinear) ∧
      ∀ B : Transducer v,
        (∀ w : List (Update v), IsLegal w → B.errorProb w ≤ ENNReal.ofReal δ) →
        ENNReal.ofReal (c * spaceFn v δ) ≤ B.expPeak + 1 ∧
        ENNReal.ofReal (c * spaceFn v δ) ≤ B.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
