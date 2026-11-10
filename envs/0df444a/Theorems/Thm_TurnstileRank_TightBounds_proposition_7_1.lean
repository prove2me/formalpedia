-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_proposition_7_1
-- name    : TurnstileRank.TightBounds.proposition_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:09:52.75664+00:00
-- url     : https://prove2.me/theorems/bb344be1-1755-4508-a307-7fbb9da03f06
-- title:
--   Proposition 7.1 — exact recovery in O(log C(U+n, n)) bits; word RAM: O(min{n log U, U log n}) bits, O(log⁴ U) update, O(log U) query
-- statement:
--   Proposition 7.1 (Exact recovery). Let n ≥ 1. On turnstile streams of final ℓ1 norm at most n, there exists a randomized linear sketching algorithm that, with probability at least 99/100, answers every rank query and every select query exactly. It uses O(log (U+n choose n)) = O(min{U log(2 + n/U), n log(2 + U/n)}) bits with random seed included, throughout updates and answering queries. Moreover, on a word RAM machine with O(log nU)-bit words, O(min{n log U, U log n}) bits of space can be achieved with O(log⁴ U) update time and O(log U) query time.
--
--   In Lean: there is $C>0$ such that for all $U,n\ge1$, with $K=\binom{U+n}{n}$: (i) $\log_2K\le C\min\{U\log_2(2+n/U),\,n\log_2(2+U/n)\}$ and conversely; (ii) there is a randomized linear sketch $L$ on $[U]$ with rank and select queries that, for every input $f\in\mathbb N^U$ with $\|f\|_1\le n$, answers every rank query $x\le U$ and every select query $r\in[0,\|f\|_1]$ exactly (error $0$) with probability at least $99/100$, with `StoredBits L (C log₂ K)`, and a bounded-memory implementation `RamExec L P n T_u T_q` (any finite times) whose memory $S\cdot w$ is at most $C\log_2K$ bits; (iii) there is such a sketch with a word-RAM implementation whose memory is at most $C\min\{n\log_2U,\,U\log_2n\}$ bits, with update time $T_u\le C\log_2^4U$ and query time $T_q\le C\log_2U$.
--
--   The fast implementation uses the printed word bound $w\le C\log_2(nU)$. The printed zero-bound cases are retained, with counterexamples recorded separately in INSIGHTS.yaml.
--
--   Differences from the source:
--   - encoding: space in bits throughout updates and answering queries, including the random seed; fast implementations on a word RAM with O(log nU)-bit words → `RamExec` gives bounded-memory execution of explicit update, rank and select programs with the seed stored in initial memory; S cells of w bits cost S·w bits throughout; `RamImpl` adds w ≤ C log₂(nU) for the fast clauses; input values fit because (U+1)(n+1) ≤ 2^w; reason: an explicit word-operation machine witnesses computation and working space; the bit-space clauses without time bounds impose no extra word-size cap; all displayed bounds retain their printed logarithms, even when zero
--   - encoding: updates (u, Δ) and select targets r ∈ [0, ‖f‖₁] given to the word RAM → Δ with −2^{w−1} ≤ Δ < 2^{w−1} (two's complement word) and select targets a/b with a, b < 2^w; the sketch-level clause covers every real target; reason: word-RAM inputs are words (the polynomial word model of §7.4 bounds update magnitudes the same way)
--   - encoding: rank and select queries answered by the decoder g_ρ → one decoder on `Query` (`rank x` or `select r`) with real answers; a select answer must be a natural number x̂ < U (`SelectOK`); reason: same answers
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: O(·) in every space and time bound; the O-equality O(log C(U+n, n)) = O(min{U log(2 + n/U), n log(2 + U/n)}) → one explicit C > 0 before U and n, and both inequalities of the equivalence; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: log (base two, §3.2) → `Real.logb 2`; reason: the paper's convention
--   - encoding: a nonempty universe and positive final-mass bound in formulas with logarithms → U ≥ 1 and n ≥ 1 (U ≥ 2 for the inverse-square-root range of Theorem 7.3); reason: exclude undefined log-zero and inverse-square-root endpoints, without removing log-one cases
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Proposition 7.1, printed p. 30 (PDF 31)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_WordRAM

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Proposition 7.1 (Exact recovery). For `n ≥ 1`: (i) `log₂ C(U+n, n)` and
`min{U log₂(2 + n/U), n log₂(2 + U/n)}` agree up to the constant `C`; (ii) a randomized linear
sketch that, with probability at least `99/100`, answers every rank query and every select query
exactly, with at most `C log₂ C(U+n, n)` bits including its seed, implemented with unrestricted running time in at most `C log₂ C(U+n, n)` bits of memory throughout updates and queries;
(iii) such a sketch implemented on a word RAM in `O(min{n log U, U log n})` bits with
`O(log⁴ U)` update time and `O(log U)` query time. -/
theorem proposition_7_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ U n : ℕ, 1 ≤ U → 1 ≤ n →
      (Real.logb 2 (Nat.choose (U + n) n) ≤
          C * min (U * Real.logb 2 (2 + (n : ℝ) / U)) (n * Real.logb 2 (2 + (U : ℝ) / n)) ∧
        min (U * Real.logb 2 (2 + (n : ℝ) / U)) (n * Real.logb 2 (2 + (U : ℝ) / n)) ≤
          C * Real.logb 2 (Nat.choose (U + n) n)) ∧
      (∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch U Ρ G Query ℝ),
        (∀ f : Fin U → ℕ, (∑ u, f u) ≤ n →
          99 / 100 ≤ prob L.law {ρ |
            (∀ x : ℕ, x ≤ U → RankOK (toZ f) 0 x (L.dec ρ (L.state ρ (toZ f)) (Query.rank x))) ∧
            (∀ r : ℝ, 0 ≤ r → r ≤ (mass (toZ f) : ℝ) →
              SelectOK (toZ f) 0 r (L.dec ρ (L.state ρ (toZ f)) (Query.select r)))}) ∧
        L.StoredBits (C * Real.logb 2 (Nat.choose (U + n) n)) ∧
        ∃ (P : RamAlg Ρ) (Tu Tq : ℕ), RamExec L P n Tu Tq ∧
          ((P.S * P.w : ℕ) : ℝ) ≤ C * Real.logb 2 (Nat.choose (U + n) n)) ∧
      (∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch U Ρ G Query ℝ),
        (∀ f : Fin U → ℕ, (∑ u, f u) ≤ n →
          99 / 100 ≤ prob L.law {ρ |
            (∀ x : ℕ, x ≤ U → RankOK (toZ f) 0 x (L.dec ρ (L.state ρ (toZ f)) (Query.rank x))) ∧
            (∀ r : ℝ, 0 ≤ r → r ≤ (mass (toZ f) : ℝ) →
              SelectOK (toZ f) 0 r (L.dec ρ (L.state ρ (toZ f)) (Query.select r)))}) ∧
        ∃ (P : RamAlg Ρ) (Tu Tq : ℕ), RamImpl L P n C Tu Tq ∧
          ((P.S * P.w : ℕ) : ℝ) ≤ C * min (n * Real.logb 2 U) (U * Real.logb 2 n) ∧
          (Tu : ℝ) ≤ C * Real.logb 2 U ^ 4 ∧ (Tq : ℝ) ≤ C * Real.logb 2 U) := by sorry

end TurnstileRank.TightBounds
