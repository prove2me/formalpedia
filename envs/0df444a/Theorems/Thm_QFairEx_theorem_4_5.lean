-- Prove2me | Theorems.Thm_QFairEx_theorem_4_5
-- name    : QFairEx.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:45.199971+00:00
-- url     : https://prove2.me/theorems/4fcdfed5-3587-4891-b398-2acec5cef9fa
-- title:
--   Theorem 4.5 — the parallel BB84 basis guessing game is won with probability at most $1/2$
-- statement:
--   For every $n\ge 1$ and every adversary $A$ — any completely positive instrument from $n$ qubits to an answer $(j,\theta^*)\in[n]\times\{0,1\}$ — the probability of winning the parallel BB84 basis guessing game of Algorithm 4.4 is at most one half:
--   $$\operatorname{win}(A)\le\tfrac12.$$
--
--   Choosing which basis bit to guess after jointly processing all $n$ challenges does not help. This is the bound that the reduction of Theorem 4.8 would violate.
--
--   Differences from the source:
--   - encoding: every adversary A (a quantum procedure answering j ∈ [n] and a guess) → every A with IsCPInstrument A, from the n qubits to Fin n × Bool with no quantum output; reason: an instrument with no quantum output is the general measurement; the index is 0-based
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Theorem 4.5, p.21

import Mathlib
import Definitions.Def_QFairEx_IsCPInstrument
import Definitions.Def_QFairEx_bb84
import Definitions.Def_QFairEx_winProb

namespace QFairEx

/-- **Theorem 4.5 (parallel BB84 basis guessing).** Chung, Lee, Raizes, Thyagarajan, *Quantum
Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883…), Theorem 4.5,
p.21: "For every integer n ≥ 1 and every adversary A, the probability that A wins the parallel
BB84 basis guessing game is at most 1/2."

Every adversary is a completely positive instrument from the `n` challenge qubits to a classical
answer `(j, θ*) ∈ Fin n × Bool` (`IsCPInstrument A`). -/
theorem theorem_4_5 (n : ℕ) (hn : 1 ≤ n)
    (A : Unit → Fin n × Bool → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ → Matrix Unit Unit ℂ)
    (hA : IsCPInstrument A) : winProb A ≤ 1 / 2 := by sorry

end QFairEx
