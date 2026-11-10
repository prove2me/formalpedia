-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_theorem_7_6
-- name    : TurnstileRank.TightBounds.theorem_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:10:06.131535+00:00
-- url     : https://prove2.me/theorems/23d50fb4-f94c-486e-aaae-6d8de8e31fd9
-- title:
--   Theorem 7.6 — priority sketch: O(ε⁻² log U log n) bits incl. an O(log nU)-bit seed, O(log U) update, O(ε⁻⁴ log² U) query
-- statement:
--   Theorem 7.6 (Full upper bound for large ε). Let (log U)^{−1/2} ≤ ε ≤ 1/8 and n ≥ 2. On turnstile streams of final ℓ1 norm at most n, there exists a randomized linear sketching algorithm that answers a fixed rank query and a fixed select query, both correct with probability at least 2/3. It uses O(ε⁻² log U log n) bits throughout updates and answering queries, including a random seed of O(log nU) bits. On a word RAM machine with O(log nU)-bit words, an update takes O(log U) time, and answering a query takes O(ε⁻⁴ log² U) time.
--
--   In Lean: there is $C>0$ such that for all $U$, $n\ge2$ and $0<\varepsilon\le1/8$ with $1\le\varepsilon^2\log_2U$ (i.e. $\varepsilon\ge(\log_2U)^{-1/2}$), there is a randomized linear sketch $L$ on $[U]$ that, for every input $f$ with $\|f\|_1\le n$, every rank query $x\le U$ and every select target $r\in[0,\|f\|_1]$, answers both correctly (error $\varepsilon\|f\|_1$) with probability at least $2/3$; with `StoredBits L (C ε⁻² log₂U log₂n)`; whose seed takes finitely many values, $\log_2(\#\text{seeds})\le C\log_2(nU)$; and with a word-RAM implementation (words of at most $C\log_2(nU)$ bits) of memory at most $C\varepsilon^{-2}\log_2U\log_2n$ bits, update time at most $C\log_2U$ and query time at most $C\varepsilon^{-4}\log_2^2U$.
--
--   Differences from the source:
--   - encoding: space in bits throughout updates and answering queries, including the random seed; fast implementations on a word RAM with O(log nU)-bit words → `RamExec` gives bounded-memory execution of explicit update, rank and select programs with the seed stored in initial memory; S cells of w bits cost S·w bits throughout; `RamImpl` adds w ≤ C log₂(nU) for the fast clauses; input values fit because (U+1)(n+1) ≤ 2^w; reason: an explicit word-operation machine witnesses computation and working space; the bit-space clauses without time bounds impose no extra word-size cap; all displayed bounds retain their printed logarithms, even when zero
--   - encoding: updates (u, Δ) and select targets r ∈ [0, ‖f‖₁] given to the word RAM → Δ with −2^{w−1} ≤ Δ < 2^{w−1} (two's complement word) and select targets a/b with a, b < 2^w; the sketch-level clause covers every real target; reason: word-RAM inputs are words (the polynomial word model of §7.4 bounds update magnitudes the same way)
--   - encoding: rank and select queries answered by the decoder g_ρ → one decoder on `Query` (`rank x` or `select r`) with real answers; a select answer must be a natural number x̂ < U (`SelectOK`); reason: same answers
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - reading: "answers a fixed rank query and a fixed select query, both correct with probability at least 2/3" → for every fixed pair (x, r), both answers are correct with probability at least 2/3 (joint event); reason: the joint reading is the stronger one and implies each query separately
--   - encoding: (log U)^{−1/2} ≤ ε → 0 < ε and 1 ≤ ε² log₂ U; reason: equivalent for ε > 0; at U = 1 both exclude every ε
--   - encoding: O(·) in every space, seed-length and time bound → one explicit C > 0 before U, n and ε; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: log (base two, §3.2) → `Real.logb 2`; reason: the paper's convention
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Theorem 7.6, printed p. 33 (PDF 34)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_WordRAM

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Theorem 7.6 (Full upper bound for large `ε`), for `(log₂ U)^{−1/2} ≤ ε ≤ 1/8` (written
`1 ≤ ε² log₂ U`) and `n ≥ 2`: a randomized linear sketch answering a fixed rank query and a fixed
select query, both correct with probability at least `2/3`, with `O(ε⁻² log U log n)` bits including
a random seed of `O(log nU)` bits, implemented on a word RAM with `O(log nU)`-bit words within that
memory, with `O(log U)` update time and `O(ε⁻⁴ log² U)` query time. -/
theorem theorem_7_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (U n : ℕ) (ε : ℝ), 0 < ε → 1 ≤ ε ^ 2 * Real.logb 2 U → ε ≤ 1 / 8 →
      2 ≤ n →
      ∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch U Ρ G Query ℝ),
        (∀ f : Fin U → ℕ, (∑ u, f u) ≤ n → ∀ x : ℕ, x ≤ U → ∀ r : ℝ, 0 ≤ r →
          r ≤ (mass (toZ f) : ℝ) →
          2 / 3 ≤ prob L.law {ρ |
            RankOK (toZ f) ε x (L.dec ρ (L.state ρ (toZ f)) (Query.rank x)) ∧
            SelectOK (toZ f) ε r (L.dec ρ (L.state ρ (toZ f)) (Query.select r))}) ∧
        L.StoredBits (C * ε⁻¹ ^ 2 * Real.logb 2 U * Real.logb 2 n) ∧
        L.law.support.Finite ∧
        Real.logb 2 (L.law.support.ncard : ℝ) ≤ C * Real.logb 2 ((n : ℝ) * U) ∧
        ∃ (P : RamAlg Ρ) (Tu Tq : ℕ), RamImpl L P n C Tu Tq ∧
          ((P.S * P.w : ℕ) : ℝ) ≤ C * ε⁻¹ ^ 2 * Real.logb 2 U * Real.logb 2 n ∧
          (Tu : ℝ) ≤ C * Real.logb 2 U ∧ (Tq : ℝ) ≤ C * ε⁻¹ ^ 4 * Real.logb 2 U ^ 2 := by sorry

end TurnstileRank.TightBounds
