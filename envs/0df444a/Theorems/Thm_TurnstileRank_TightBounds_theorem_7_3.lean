-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_theorem_7_3
-- name    : TurnstileRank.TightBounds.theorem_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:10:00.031028+00:00
-- url     : https://prove2.me/theorems/1f517d66-05a8-43ca-bba3-dc0e26bcb94a
-- title:
--   Theorem 7.3 — refined Dyadic CountSketch: O(ε⁻¹L^{3/2} log(2 + nε/√L)) bits; word RAM: O(ε⁻¹L^{3/2} log n) bits, O(log² U) update and query
-- statement:
--   Theorem 7.3 (Upper bound for small ε). Let 2/U ≤ ε ≤ (log U)^{−1/2} and L = ⌈log(Uε)⌉. On turnstile streams of final ℓ1 norm at most n, there exists a randomized linear sketching algorithm that answers a fixed rank query and a fixed select query, both correct with probability at least 2/3. It uses O(ε⁻¹L^{3/2} log(2 + nε/√L)) bits (7.1) with random seed included, throughout updates and answering queries. Moreover, on a word RAM machine with O(log nU)-bit words, O(ε⁻¹L^{3/2} log n) bits of space can be achieved with O(log² U) update time and O(log² U) query time.
--
--   In Lean: there is $C>0$ such that for all $U\ge2$, $n\ge1$ and $2/U\le\varepsilon\le(\log_2U)^{-1/2}$, with $L=\lceil\log_2(U\varepsilon)\rceil$: (i) there is a randomized linear sketch $L'$ on $[U]$ that, for every input $f$ with $\|f\|_1\le n$, every rank query $x\le U$ and every select target $r\in[0,\|f\|_1]$, answers both correctly (error $\varepsilon\|f\|_1$) with probability at least $2/3$, with `StoredBits` at most $C\varepsilon^{-1}L^{3/2}\log_2(2+n\varepsilon/\sqrt L)$ and a bounded-memory implementation `RamExec` (any finite times) whose memory is within the same bound; (ii) there is such a sketch with a word-RAM implementation of memory at most $C\varepsilon^{-1}L^{3/2}\log_2n$ bits, update time at most $C\log_2^2U$ and query time at most $C\log_2^2U$.
--
--   The fast implementation uses the printed word bound $w\le C\log_2(nU)$. The printed zero-bound cases are retained, with counterexamples recorded separately in INSIGHTS.yaml.
--
--   Differences from the source:
--   - encoding: space in bits throughout updates and answering queries, including the random seed; fast implementations on a word RAM with O(log nU)-bit words → `RamExec` gives bounded-memory execution of explicit update, rank and select programs with the seed stored in initial memory; S cells of w bits cost S·w bits throughout; `RamImpl` adds w ≤ C log₂(nU) for the fast clauses; input values fit because (U+1)(n+1) ≤ 2^w; reason: an explicit word-operation machine witnesses computation and working space; the bit-space clauses without time bounds impose no extra word-size cap; all displayed bounds retain their printed logarithms, even when zero
--   - encoding: updates (u, Δ) and select targets r ∈ [0, ‖f‖₁] given to the word RAM → Δ with −2^{w−1} ≤ Δ < 2^{w−1} (two's complement word) and select targets a/b with a, b < 2^w; the sketch-level clause covers every real target; reason: word-RAM inputs are words (the polynomial word model of §7.4 bounds update magnitudes the same way)
--   - encoding: rank and select queries answered by the decoder g_ρ → one decoder on `Query` (`rank x` or `select r`) with real answers; a select answer must be a natural number x̂ < U (`SelectOK`); reason: same answers
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - reading: "answers a fixed rank query and a fixed select query, both correct with probability at least 2/3" → for every fixed pair (x, r), the rank answer at x and the select answer at r are both correct with probability at least 2/3 (joint event); reason: the joint reading is the stronger one and implies each query separately
--   - reading: 2/U ≤ ε ≤ (log U)^{−1/2}, where (log U)^{−1/2} is undefined at U = 1 → 2 ≤ U and 2/U ≤ ε ≤ 1/√(log₂ U); reason: the range is meant for U ≥ 2 (at U = 1 the upper end is 1/0)
--   - encoding: O(·) in every space and time bound → one explicit C > 0 before U, n and ε; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: log (base two, §3.2) → `Real.logb 2`; reason: the paper's convention
--   - encoding: a nonempty universe and positive final-mass bound in formulas with logarithms → U ≥ 1 and n ≥ 1 (U ≥ 2 for the inverse-square-root range of Theorem 7.3); reason: exclude undefined log-zero and inverse-square-root endpoints, without removing log-one cases
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Theorem 7.3, printed p. 31 (PDF 32)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_WordRAM

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Theorem 7.3 (Upper bound for small `ε`), with `L = ⌈log₂(Uε)⌉`, for `2/U ≤ ε ≤ (log₂ U)^{−1/2}`:
a randomized linear sketch answering a fixed rank query and a fixed select query, both correct with
probability at least `2/3`, with `O(ε⁻¹ L^{3/2} log₂(2 + nε/√L))` bits including its seed, also
throughout updates and queries; and on a word RAM with `O(log nU)`-bit words,
`O(ε⁻¹ L^{3/2} log₂ n)` bits with `O(log² U)` update and query time. -/
theorem theorem_7_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (U n : ℕ) (ε : ℝ), 2 ≤ U → 1 ≤ n → 2 / (U : ℝ) ≤ ε →
      ε ≤ 1 / Real.sqrt (Real.logb 2 U) →
      (∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch U Ρ G Query ℝ),
        (∀ f : Fin U → ℕ, (∑ u, f u) ≤ n → ∀ x : ℕ, x ≤ U → ∀ r : ℝ, 0 ≤ r →
          r ≤ (mass (toZ f) : ℝ) →
          2 / 3 ≤ prob L.law {ρ |
            RankOK (toZ f) ε x (L.dec ρ (L.state ρ (toZ f)) (Query.rank x)) ∧
            SelectOK (toZ f) ε r (L.dec ρ (L.state ρ (toZ f)) (Query.select r))}) ∧
        L.StoredBits (C * ε⁻¹ * (⌈Real.logb 2 (U * ε)⌉ : ℝ) ^ ((3 : ℝ) / 2) *
          Real.logb 2 (2 + n * ε / Real.sqrt (⌈Real.logb 2 (U * ε)⌉ : ℝ))) ∧
        ∃ (P : RamAlg Ρ) (Tu Tq : ℕ), RamExec L P n Tu Tq ∧
          ((P.S * P.w : ℕ) : ℝ) ≤ C * ε⁻¹ * (⌈Real.logb 2 (U * ε)⌉ : ℝ) ^ ((3 : ℝ) / 2) *
            Real.logb 2 (2 + n * ε / Real.sqrt (⌈Real.logb 2 (U * ε)⌉ : ℝ))) ∧
      (∃ (Ρ G : Type) (_ : AddCommGroup G) (L : LinearSketch U Ρ G Query ℝ),
        (∀ f : Fin U → ℕ, (∑ u, f u) ≤ n → ∀ x : ℕ, x ≤ U → ∀ r : ℝ, 0 ≤ r →
          r ≤ (mass (toZ f) : ℝ) →
          2 / 3 ≤ prob L.law {ρ |
            RankOK (toZ f) ε x (L.dec ρ (L.state ρ (toZ f)) (Query.rank x)) ∧
            SelectOK (toZ f) ε r (L.dec ρ (L.state ρ (toZ f)) (Query.select r))}) ∧
        ∃ (P : RamAlg Ρ) (Tu Tq : ℕ), RamImpl L P n C Tu Tq ∧
          ((P.S * P.w : ℕ) : ℝ) ≤
            C * ε⁻¹ * (⌈Real.logb 2 (U * ε)⌉ : ℝ) ^ ((3 : ℝ) / 2) * Real.logb 2 n ∧
          (Tu : ℝ) ≤ C * Real.logb 2 U ^ 2 ∧ (Tq : ℝ) ≤ C * Real.logb 2 U ^ 2) := by sorry

end TurnstileRank.TightBounds
