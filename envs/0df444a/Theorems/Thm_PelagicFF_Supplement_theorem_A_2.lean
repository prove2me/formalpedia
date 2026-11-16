-- Prove2me | Theorems.Thm_PelagicFF_Supplement_theorem_A_2
-- name    : PelagicFF.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:31:24.381219+00:00
-- url     : https://prove2.me/theorems/e83f6a21-6dc6-4507-880e-6a6e02f5169d
-- title:
--   Theorem A.2 — $\mathrm{GHS}_n$: exact $n$-qubit protocol, $\Theta(n^2)$ bits classically
-- statement:
--   Let $\mathrm{GHS}_n$ be the Graph Hadamard Support Problem (Problem A.1): Alice holds a symmetric zero-diagonal $A\in\mathbb F_2^{n\times n}$, Bob holds $S\subseteq[n]$, and Bob must output $z$ with $|\langle z|H_S|\psi_A\rangle|^2>0$. Then:
--
--   1. For every $n$ there is a quantum one-way protocol with $n$-qubit messages that succeeds with probability $1$ on every input.
--   2. There are $c>0$ and $n_0$ such that for every $n\ge n_0$, every randomized one-way protocol with $m$-bit messages that succeeds with probability at least $2/3$ on every input satisfies $m\ge c\,n^2$.
--   3. There are $C$ and $n_0$ such that for every $n\ge n_0$ there is an exact deterministic classical one-way protocol with at most $C\,n^2$ bits.
--
--   So $\mathrm{GHS}_n$ separates $n$ qubits from $\Theta(n^2)$ classical bits, with a stabilizer-state message and a product Hadamard measurement.
--
--   **Formalization Note** "Succeeds with probability at least $2/3$" is worst case over inputs, as in §2.1.
--
--   Differences from the source:
--   - encoding: quantum one-way protocol with m qubits, shared randomness, no entanglement → published PelagicFF.OneWayQProtocol: finite coin law, density operator on Fin m → Bool per (coin, Alice input), POVM per (coin, Bob input); reason: the model of §2.1, p.14; same protocols
--   - encoding: randomized public-coin one-way protocol communicating c bits → OneWayProtocol: finite coin law, Alice's c-bit message Fin c → Bool per (coin, input), Bob's output per (coin, message, input); reason: the model of §2.1, p.14 and pp.45, 60 (a c-bit message takes at most 2^c values); private coins are subsumed by public coins
--   - encoding: a deterministic one-way protocol communicating c bits → DetOneWayProtocol: msg : X → (Fin c → Bool), out : (Fin c → Bool) → Y → Z; reason: the model of pp.45 and 59
--   - encoding: Ω(n²), O(n²) → ∃ constants and a threshold n₀ chosen before n and the protocol; reason: standard meaning of the asymptotic notation
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem A.2, p.57; §A.1, p.58

import Mathlib
import Definitions.Def_PelagicFF_OneWayQProtocol
import Definitions.Def_PelagicFF_Supplement_OneWayProtocol
import Definitions.Def_PelagicFF_Supplement_DetOneWayProtocol
import Definitions.Def_PelagicFF_Supplement_GHS

namespace PelagicFF.Supplement

/-- **Theorem A.2.** Anselm, Ding, Gilboa, Grewal, *Optimal and Verifiable Quantum Advantages in
Communication Complexity*, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem A.2, p.57:

"There is an exact one-way communication protocol for GHSₙ using n qubits. Furthermore, every
randomized one-way protocol for GHSₙ that succeeds with probability at least 2/3 uses Ω(n²) bits of
communication. Lastly, there exists an exact deterministic classical one-way protocol that uses
O(n²) bits of communication."

The three clauses: (a) for every `n`, an `n`-qubit quantum one-way protocol with success
probability `1` on every input; (b) `Ω(n²)` against every randomized one-way protocol succeeding
with probability `≥ 2/3` on every input; (c) an exact deterministic one-way protocol with `O(n²)`
bits.

**Formalization Note.** "Succeeds with probability at least 2/3" is worst case over inputs (§2.1,
p.14). `Ω`/`O` are `∃` constants and a threshold fixed before `n` and the protocol. -/
theorem theorem_A_2 :
    (∀ n : ℕ, ∃ P : PelagicFF.OneWayQProtocol (SymZeroDiag n) (Finset (Fin n)) (Fin n → Bool) n,
      ∀ A S, P.succProb (GHS n) A S = 1) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      ∀ P : OneWayProtocol (SymZeroDiag n) (Finset (Fin n)) (Fin n → Bool) m,
        (∀ A S, (2 : ℝ) / 3 ≤ P.succProb (GHS n) A S) → c * (n : ℝ) ^ 2 ≤ (m : ℝ)) ∧
    (∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ m : ℕ, (m : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
      ∃ P : DetOneWayProtocol (SymZeroDiag n) (Finset (Fin n)) (Fin n → Bool) m,
        P.IsExact (GHS n)) := by sorry

end PelagicFF.Supplement
