-- Prove2me | Theorems.Thm_TimeSpaceMA_theorem_3_1
-- name    : TimeSpaceMA.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:24.350184+00:00
-- url     : https://prove2.me/theorems/a63f52a4-599d-42ba-9f5e-0ed61ffd80be
-- title:
--   Theorem 3.1 — every $\mathrm{DTISP}[t,s]$ language has an MA protocol with message and verifier time $\max\{N,t^{3/4}N^{1/8}S^{1/2},t^{1/3}N^{2/3}S^{1/6}\}t^\varepsilon$
-- statement:
--   Let $L\in\mathrm{DTISP}[t(n),s(n)]$ for $t(n)\ge n$. Let $S=s+O(\log nt)$ be the number of bits in a configuration of the machine deciding $L$, and $N=\max\{n,S^2\}$. For every $\varepsilon>0$, $L$ has a Merlin–Arthur protocol with perfect completeness and soundness $1/3$, where Merlin's message length and Arthur's running time are both
--   $$\max\{N,\ t^{3/4}N^{1/8}S^{1/2},\ t^{1/3}N^{2/3}S^{1/6}\}\,t^\varepsilon,$$
--   Arthur uses $(2+\varepsilon)\log t$ random bits, and Merlin's running time is $t^{1/2+\omega/4+\varepsilon}n^{1/2}\,\mathrm{poly}(s+\log t)$, where $\omega$ is the matrix multiplication exponent.
--
--   For superpolynomial $t$ and $s=t^{o(1)}$, the message and the verifier's time are $t^{3/4+o(1)}$: an arbitrary small-space computation of length $t$ has a non-interactive proof checkable in polynomially less than $t$ time.
--
--   **Formalization Note** Arthur and Merlin are single finite programs of a log-cost RAM. They are chosen after $\varepsilon$ and depend on no input.
--
--   Differences from the source:
--   - encoding: deterministic Turing machine with random-access input → TimeSpaceMA.RATM: finite states and alphabet, k work tapes, saturating address register, space = scanned cells; reason: the page fixes no further details
--   - encoding: "algorithm", "running time" of Arthur and Merlin; "Merlin's message length" → finite programs of a log-cost RAM (TimeSpaceMA.Program), with work, the cursor, and M[0]-length output; reason: the page names no machine; the model is polylog-equivalent to a word RAM with Θ(log T)-bit words, and t^ε absorbs polylog factors
--   - reading: Theorem 3.1 names no constructibility, while the abstract does and the proof computes parameters from T → no constructibility hypothesis on t; reason: the printed theorem is the stronger reading; a header in Merlin's message carrying the true running time and space replaces constructibility, and soundness does not depend on it (see paper.md, decision 4, and MODERATION_NOTES.md)
--   - reading: S = s + O(log nt) → S = s + log₂(nt + 2), coefficient 1; reason: the bound is polynomial in S, so a constant factor in S is absorbed by C; this is the strongest form
--   - encoding: the bound has no printed constant → C > 0 after ε, before x; K for poly after ε; reason: the proof on p.23 gives the bound up to a constant factor and for large t; C·t^{ε/2} ≤ t^ε for large t, and t ≥ n grows with n
--   - reading: ω, the matrix multiplication exponent, of unnamed field → ω = OAI omega ℂ; reason: it is the field of the published bound 9/4 (Fact 3.22), and formally the smallest such ω
--   - reading: Arthur's running time, coins and message length → ∃ m(n) ≤ B, with time and coins for every tape and every π of length at most m(n), honest message of length at most m(n), and soundness for every π of any length; reason: messages of a protocol live in that set; a bound over all π cannot be enforced without computing m, and soundness stays universal
--   - reading: (2 + ε) log t random bits → cursor ≤ (2 + ε) log₂ t(n) on every tape, with no additive constant; reason: the proof gives µ = (2 + o(1)) log₂ K, and at small t Arthur reads no coin
--   - generalization: "Merlin's running time" (Merlin matters only for x ∈ L) → the work bound holds on every input x, with the valid message only for x ∈ L; reason: the bound on every x implies it on x ∈ L, and it holds since the honest Merlin simulates M first
--   - encoding: t(n) ≥ n, n^{1/2}, poly(s + log t) → 1 ≤ t(n) added, (max n 1)^{1/2}, (s + log₂ t + 2)^K; reason: they remove the junk values 0^ε = 0 and 0^K = 0; no instance with n ≥ 1, t ≥ 2 changes
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem 3.1, p.6; Definition 2.1, pp.5–6; §3.7, p.23

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_TimeSpaceMA_InDTISP
import Definitions.Def_TimeSpaceMA_ArthurAccepts
import Definitions.Def_TimeSpaceMA_timeSpaceE

open MeasureTheory

namespace TimeSpaceMA

/-- **Theorem 3.1** (Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027
submission, manuscript sha256 184c2f95…, p.6). Every `L ∈ DTISP[t, s]` with `t(n) ≥ n` has, for every
`ε > 0`, an MA protocol with perfect completeness and soundness `1/3`, message length and Arthur's time
`max{N, t^{3/4}N^{1/8}S^{1/2}, t^{1/3}N^{2/3}S^{1/6}} t^ε`, `(2 + ε) log t` coins, and Merlin's time
`t^{1/2+ω/4+ε} n^{1/2} poly(s + log t)`.

**Formalization Note** Arthur and Merlin are finite programs of the log-cost RAM, chosen after `ε` and
before `x`. No time-constructibility of `t` is assumed, as on the page (`paper.md`, decision 4).
`S = s + log₂(nt + 2)` with coefficient 1 (decision 6), and `C` follows `ε` (decision 5). Arthur's time
and coins are stated for every coin tape and every `π` with `|π| ≤ m(n) ≤ B` (decision 8); soundness holds for
every `π` of any length. `ω = ω_ℂ` (decision 7). `t(n) ≥ 1`, `max n 1` and the `+ 2` remove the junk
values `0^ε = 0` (decision 10). Merlin's time holds on every input. -/
theorem theorem_3_1 (L : Set (List Bool)) (t s : ℕ → ℕ) (ht : ∀ n, n ≤ t n ∧ 1 ≤ t n)
    (hL : InDTISP L t s) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Arthur Merlin : Program) (m : ℕ → ℕ) (C : ℝ) (K : ℕ), 0 < C ∧ Merlin.CoinFree ∧
      ∀ x : List Bool,
        let n := x.length
        let S : ℝ := (s n : ℝ) + Real.logb 2 ((n : ℝ) * (t n : ℝ) + 2)
        let N : ℝ := max (n : ℝ) (S ^ 2)
        let B : ℝ := C * timeSpaceE (t n : ℝ) N S * (t n : ℝ) ^ ε
        (m n : ℝ) ≤ B ∧
        (∀ π : List Bool, π.length ≤ m n → ∀ τ : ℕ → Bool,
          ∃ st, Arthur.RunsTo τ (arthurMem x π) st ∧ (st.work : ℝ) ≤ B ∧
            (st.cursor : ℝ) ≤ (2 + ε) * Real.logb 2 (t n : ℝ)) ∧
        (∃ st, Merlin.RunsTo zeroTape (merlinMem x) st ∧
          (st.work : ℝ) ≤ C *
              (t n : ℝ) ^ ((1 : ℝ) / 2 + OAI.MatrixMultiplication.Arithmetic.omega ℂ / 4 + ε) *
              (max (n : ℝ) 1) ^ ((1 : ℝ) / 2) *
              ((s n : ℝ) + Real.logb 2 (t n : ℝ) + 2) ^ K ∧
          (x ∈ L → (merlinOutput st.mem).length ≤ m n ∧
            ∀ τ : ℕ → Bool, ArthurAccepts Arthur x (merlinOutput st.mem) τ)) ∧
        (x ∉ L → ∀ π : List Bool, coinTape {τ | ArthurAccepts Arthur x π τ} ≤ 1 / 3) := by sorry

end TimeSpaceMA
