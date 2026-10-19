-- Prove2me | Theorems.Thm_QAlgorithms_Papers_CDNT98_convey_bits_needs_half_qubits
-- name    : QAlgorithms.Papers.CDNT98.convey_bits_needs_half_qubits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:49:22.167912+00:00
-- url     : https://prove2.me/theorems/5751a819-b4fa-4ab5-9481-a80b3ffe18cd
-- title:
--   CDNT Theorem 1: conveying n bits (or m bits of mutual information) with entanglement needs ⌈n/2⌉ (⌈m/2⌉) qubits from Alice
-- statement:
--   This is the entanglement-assisted lower bound of Cleve, van Dam, Nielsen and Tapp, a consequence of Holevo's theorem.
--
--   Consider a two-party qubit protocol in which Alice holds an input $x\in\{0,1\}^n$ on $n$ of her qubits. All other qubits start in $|0\rangle$, except for a block of qubits in an arbitrary shared state $|\Phi\rangle$ (fixed before the input, its qubits distributed between Alice and Bob in any way). The protocol is a fixed sequence of steps, each of which is a unitary applied by one party to qubits it currently holds, or the sending of one qubit to the other party. Let $n_{AB}$ be the number of qubits Alice sends to Bob; the number $n_{BA}$ of qubits Bob sends to Alice is unrestricted. At the end Bob performs a measurement (a POVM) acting only on the qubits he holds.
--
--   1. If Bob's measurement, with outcomes in $\{0,1\}^n$, returns $x$ with probability $1$ for every input $x$, then
--   $$
--   n_{AB}\ \ge\ \left\lceil \tfrac{n}{2}\right\rceil.
--   $$
--   2. More generally, let $X$ be uniformly distributed on $\{0,1\}^n$ and $Y$ the outcome of any measurement of Bob. For every natural number $m$, if $I(X:Y)\ge m$ (mutual information in bits), then $n_{AB}\ge\lceil m/2\rceil$.
--
--   The bound holds regardless of the prior entanglement and of the communication from Bob to Alice. It is the information-theoretic ingredient of the paper's linear lower bounds on the communication complexity of the inner product function.
--
--   **Formalization Note** The protocol model is the shared `TwoPartyProtocol` (pure shared state; mixed states and intermediate measurements are simulated with ancillas, as the paper notes on p.13). The ceiling $\lceil k/2\rceil$ is written as natural-number division $(k+1)/2$. In clause 1 the outcome set is $\{0,1\}^n$ itself; a measurement with another outcome set followed by a decoding map is a coarse-grained measurement of this form, and clause 2 covers arbitrary outcome sets.
-- source:
--   Quantum entanglement and the communication complexity of the inner product function (Cleve, van Dam, Nielsen, Tapp), arXiv:quant-ph/9708019v3, Theorem 1, PDF p. 3. https://arxiv.org/abs/quant-ph/9708019v3 . PDF SHA-256: 946b24fcc2da9e56775de4b60d5351bbbf77a74672218413178d65d0d5c1c79c.

import Definitions.Def_QAlgorithms_Defs_QuantumInformation
set_option autoImplicit false

namespace QAlgorithms.Papers.CDNT98

universe u

/-- CDNT, Theorem 1 (p.3; it follows from Theorem 2, p.12, by the remark after it).

For every valid two-party protocol on Alice's `n` input bits, with an arbitrary prior shared state
and arbitrary qubit communication from Bob to Alice:
1. if Bob's final measurement (outcome set `{0,1}^n`, acting on his qubits) returns `x` with
   probability `1` for every input `x` (Alice conveys her `n` bits), then Alice sends Bob at least
   `⌈n/2⌉` qubits;
2. for every measurement of Bob and every natural `m`, if the mutual information between the
   uniformly distributed `X` and Bob's outcome is at least `m` bits, then Alice sends Bob at least
   `⌈m/2⌉` qubits. -/
theorem convey_bits_needs_half_qubits {n : ℕ} (P : TwoPartyProtocol n) (hP : P.IsValid) :
    (∀ M : Qubits n → Matrix (Qubits P.N) (Qubits P.N) ℂ, P.IsBobMeasurement M →
        (∀ x : Qubits n, P.outcomeProb M x x = 1) → (n + 1) / 2 ≤ P.nAB) ∧
      (∀ (Y : Type u) [Fintype Y] (M : Y → Matrix (Qubits P.N) (Qubits P.N) ℂ),
        P.IsBobMeasurement M → ∀ m : ℕ, (m : ℝ) ≤ P.mutualInfo M → (m + 1) / 2 ≤ P.nAB) := by
  sorry



end QAlgorithms.Papers.CDNT98
