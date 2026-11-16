-- Prove2me | Theorems.Thm_PelagicFF_Supplement_theorem_A_10
-- name    : PelagicFF.Supplement.theorem_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:32:27.379081+00:00
-- url     : https://prove2.me/theorems/38c7b0e4-d812-4e1e-bd02-170145897402
-- title:
--   Theorem A.10 — randomized one-way protocols for $\mathrm{GHS}_n$ need $\Omega(n^2)$ bits
-- statement:
--   Let $\mathrm{GHS}_n$ be the Graph Hadamard Support Problem (Problem A.1). There are $c>0$ and $n_0$ such that for every $n\ge n_0$, every randomized public-coin one-way protocol with $m$-bit messages that solves $\mathrm{GHS}_n$ with success probability at least $2/3$ on every input $(A,S)$ satisfies
--
--   $$
--   m\ \ge\ c\,n^2 .
--   $$
--
--   Together with the $n$-qubit exact quantum protocol of Theorem A.2 this gives the $n$ versus $\Omega(n^2)$ separation.
--
--   **Formalization Note** "Solves with success probability at least $2/3$" is worst case over inputs, as in §2.1.
--
--   Differences from the source:
--   - encoding: randomized public-coin one-way protocol communicating c bits → OneWayProtocol: finite coin law, Alice's c-bit message Fin c → Bool per (coin, input), Bob's output per (coin, message, input); reason: the model of §2.1, p.14 and pp.45, 60 (a c-bit message takes at most 2^c values); private coins are subsumed by public coins
--   - encoding: Ω(n²) → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, chosen before n and the protocol; reason: standard meaning of the asymptotic notation
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem A.10, p.60

import Mathlib
import Definitions.Def_PelagicFF_Supplement_OneWayProtocol
import Definitions.Def_PelagicFF_Supplement_GHS

namespace PelagicFF.Supplement

/-- **Theorem A.10.** Anselm, Ding, Gilboa, Grewal, *Optimal and Verifiable Quantum Advantages in
Communication Complexity*, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem A.10, p.60:

"Any classical randomized one-way protocol that solves GHSₙ with success probability at least 2/3
requires Ω(n²) bits of communication."

**Formalization Note.** "Solves with success probability at least 2/3" is worst case over inputs
(§2.1, p.14). `Ω(n²)`: one constant `c > 0` and one threshold `n₀`, fixed before `n` and the
protocol. -/
theorem theorem_A_10 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      ∀ P : OneWayProtocol (SymZeroDiag n) (Finset (Fin n)) (Fin n → Bool) m,
        (∀ A S, (2 : ℝ) / 3 ≤ P.succProb (GHS n) A S) → c * (n : ℝ) ^ 2 ≤ (m : ℝ) := by sorry

end PelagicFF.Supplement
