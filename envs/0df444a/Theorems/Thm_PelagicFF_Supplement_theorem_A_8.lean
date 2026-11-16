-- Prove2me | Theorems.Thm_PelagicFF_Supplement_theorem_A_8
-- name    : PelagicFF.Supplement.theorem_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:31:54.179628+00:00
-- url     : https://prove2.me/theorems/a6a2e65c-c417-449e-a960-db68a300f868
-- title:
--   Theorem A.8 — exact deterministic one-way protocols for $\mathrm{GHS}_n$ need $\Omega(n^2)$ bits
-- statement:
--   Let $\mathrm{GHS}_n$ be the Graph Hadamard Support Problem (Problem A.1). There are $c>0$ and $n_0$ such that for every $n\ge n_0$, every deterministic one-way protocol with $m$-bit messages that solves $\mathrm{GHS}_n$ with success probability $1$ (Bob's output lies in $\operatorname{supp}(H_S|\psi_A\rangle)$ for every input $(A,S)$) satisfies
--
--   $$
--   m\ \ge\ c\,n^2 .
--   $$
--
--   This is the exact deterministic case of the lower bound of Theorem A.2.
--
--   Differences from the source:
--   - encoding: a deterministic one-way protocol communicating c bits → DetOneWayProtocol: msg : X → (Fin c → Bool), out : (Fin c → Bool) → Y → Z; reason: the model of pp.45 and 59
--   - encoding: Ω(n²) → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, chosen before n and the protocol; reason: standard meaning of the asymptotic notation
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem A.8, p.58

import Mathlib
import Definitions.Def_PelagicFF_Supplement_DetOneWayProtocol
import Definitions.Def_PelagicFF_Supplement_GHS

namespace PelagicFF.Supplement

/-- **Theorem A.8.** Anselm, Ding, Gilboa, Grewal, *Optimal and Verifiable Quantum Advantages in
Communication Complexity*, arXiv:2610.05585 (held version, sha256 4564aef3…), Theorem A.8, p.58:

"Any classical deterministic one-way protocol that solves GHSₙ with success probability 1 requires
Ω(n²) bits of communication."

**Formalization Note.** `Ω(n²)`: one constant `c > 0` and one threshold `n₀`, fixed before `n` and
the protocol. Success probability `1` of a deterministic protocol is correctness on every input. -/
theorem theorem_A_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      ∀ P : DetOneWayProtocol (SymZeroDiag n) (Finset (Fin n)) (Fin n → Bool) m,
        P.IsExact (GHS n) → c * (n : ℝ) ^ 2 ≤ (m : ℝ) := by sorry

end PelagicFF.Supplement
