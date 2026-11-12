-- Prove2me | Theorems.Thm_RTStringIndex_Main_theorem_1
-- name    : RTStringIndex.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:37.453294+00:00
-- url     : https://prove2.me/theorems/c77fb9f1-c574-4e2e-837d-6ece79cf43e7
-- title:
--   Theorem 1 — real-time string indexing: $O(1)$ per letter w.p. $1-n^{-c}$, $O(|P|+\mathrm{occ})$ queries, $O(n)$ words
-- statement:
--   There are one program $Q$ of the online randomized word RAM and constants $c_0$, $C_{\mathrm{space}}$, $C_{\mathrm{query}}$ with the following property. Fix any bound $N$ on the number of appends, any word size $W\ge c_0\lceil\log_2(N+2)\rceil$, and any stream of appends and pattern queries, fixed in advance, whose letters and pattern lengths are below $2^W$. Then, on every random tape:
--
--   1. the run reaches every operation;
--   2. each query $P$, asked when the current text is $T$, outputs exactly the occurrences of $P$ in $T$ (0-based start positions), each once, within $C_{\mathrm{query}}(|P|+\mathrm{occ}+1)$ steps;
--   3. every memory cell touched up to the end of an operation is below $C_{\mathrm{space}}(n+1)$, where $n$ is the length of the text after that operation.
--
--   Moreover, for every constant $c>0$ there is a constant $C_c$ such that, for all such $N$, $W$ and streams, every append satisfies
--   $$\Pr_\omega\bigl[\text{the append takes more than } C_c \text{ steps}\bigr]\le n^{-c},$$
--   where $n$ is the length of the text after the append.
--
--   This is the first index for a text over an arbitrary integer alphabet, given online, that spends $O(1)$ worst-case time per letter with high probability and answers reporting queries in optimal $O(|P|+\mathrm{occ})$ time. Earlier solutions had super-constant time per letter or a constant-size alphabet.
--
--   Differences from the source:
--   - encoding: the word RAM → the online randomized word RAM of DynConnWC_Program: unit-cost arithmetic and bit operations on W-bit words, indirect access, online reads, writes, and a tape of independent uniform words; reason: the source names no instruction set; this is the platform's established machine
--   - encoding: a data structure processing letters and queries given online → one program reading the input words of a stream (append: 0, a; query: 1, |P|, P); an operation's time is the number of steps between the reads of its first word and of the next operation's first word, its output the words written in that window; reason: this makes worst-case time per online operation a statement about one run
--   - reading: T given online, one letter at a time → letters are appended at the right end; reason: abstract, p.1: “each new letter appended to T”; the reversed framework of p.2 is internal
--   - reading: for any constant c > 0, each new letter in O(1) time with probability ≥ 1 − n^{−c} → the program and the space and query constants are chosen before c; the stream is fixed before the tape; for each append, Pr[time > C_c] ≤ n^{−c} with n the length after the append; reason: the quantifier order of the theorem; an oblivious stream is standard for the w.h.p. dictionary bounds of [10]
--   - reading: O(n) words of space; report all occurrences in O(|P| + occ) worst-case time → on every tape: the cells touched up to the end of each operation are below C_space(n + 1), and each query outputs a duplicate-free list whose set is occ(P, T) within C_query(|P| + occ + 1) steps; reason: Theorem 1 qualifies only the letter time with a probability; this is the stronger reading; space in words is bounded by the addresses used
--   - encoding: an integer alphabet of arbitrary size, on the word RAM → letters and pattern lengths below 2^W, and W ≥ c₀⌈log₂(N + 2)⌉ for a bound N on the number of appends; reason: letters fit in a word; the word size is Θ(log n) or larger
--   - encoding: O(·) bounds → explicit constants; the +1 covers |P| + occ = 0 and n = 0; reason: Lean has no asymptotic notation
--   - encoding: occurrences of P in T (positions of T counted from 1, p.7) → the 0-based start positions i ≤ |T| such that P is a prefix of T[i..]; reason: index convention; same occurrences
--   - generalization: a pattern P → every pattern, including the empty one (which occurs at all n + 1 positions); reason: covers the source's patterns
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Theorem 1, p. 2; abstract, p. 1; §10, p. 24; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_Machine

set_option autoImplicit false

open DynConnWC MeasureTheory

namespace RTStringIndex.Main

/-- **Theorem 1.** Kucherov, Nekrich, *Real-Time String Indexing in Optimal Time*, STOC 2027
submission #1543 (October 2026), p.2. "Let T be a text over an integer alphabet of arbitrary size
that is given online, one letter at a time, and let n denote the current length of T. On the word
RAM, there is a data structure that uses O(n) words of space and, for any constant c > 0,
processes each new letter in O(1) worst-case time with probability at least 1 − n^{−c}. At any
moment, given a pattern P, it can report all occ occurrences of P in the current text T in
O(|P| + occ) worst-case time."

**Formalization Note.** One program `Q` and constants `c₀, C_space, C_query` are chosen first; the
per-letter constant `C_c` is chosen after `c`. For every bound `N` on the number of appends, every
word size `W ≥ c₀⌈log₂(N + 2)⌉` and every stream `σ` (fixed before the tape) whose letters and
pattern lengths fit in a word: on every tape the run reaches every operation, each query outputs
exactly its occurrences (`0`-based start positions in the current text), each once, within
`C_query(|P| + occ + 1)` steps, and the cells touched up to the end of operation `t` are below
`C_space(n_t + 1)`; and for each append the probability that it takes more than `C_c` steps is at
most `n^{−c}`, with `n` the text length after the append. -/
theorem theorem_1 :
    ∃ (Q : Program) (c₀ Cspace Cquery : ℕ),
      (∀ (N W : ℕ), c₀ * Nat.clog 2 (N + 2) ≤ W → ∀ σ : List Op, numAppends σ ≤ N →
        WordsFit W σ → ∀ ω : ℕ → Fin (2 ^ W),
          RunsThrough W Q ω σ ∧
          (∀ (t : ℕ) (ht : t < σ.length) (P : List ℕ), σ[t] = Op.query P →
            (opOutput W Q ω σ t).Nodup ∧
            (opOutput W Q ω σ t).toFinset = occ P (textAfter σ t) ∧
            opTime W Q ω σ t ≤ Cquery * (P.length + (occ P (textAfter σ t)).card + 1)) ∧
          (∀ t, t < σ.length → ∀ a ∈ addrsUpTo W Q ω σ t,
            a < Cspace * ((textAfter σ (t + 1)).length + 1))) ∧
      (∀ c : ℝ, 0 < c → ∃ Cc : ℕ, ∀ (N W : ℕ), c₀ * Nat.clog 2 (N + 2) ≤ W →
        ∀ σ : List Op, numAppends σ ≤ N → WordsFit W σ →
          ∀ (t : ℕ) (ht : t < σ.length) (a : ℕ), σ[t] = Op.append a →
            tapeLaw W {ω | Cc < opTime W Q ω σ t} ≤
              ENNReal.ofReal (((textAfter σ (t + 1)).length : ℝ) ^ (-c))) := by sorry

end RTStringIndex.Main
