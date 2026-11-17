-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_6
-- name    : QuantumLTF.Membership.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:44:56.508101+00:00
-- url     : https://prove2.me/theorems/8d1258ac-9ee6-4584-bcaa-b8220434a5b3
-- title:
--   Theorem 4.6 — lower bound $Q=\Omega(\log k)$ under the promise $1\le|A|\le k$
-- statement:
--   There is a universal constant $c>0$ such that for every $n\ge k\ge2$,
--   $$Q_n(1\le|A|\le k)\ge c\log k ,$$
--   where $Q_n$ is the bounded-error quantum query complexity of learning the Majority junta (Definition 2.2). Together with Theorem 4.5 it gives part (ii) of Theorem 4.1.
--
--   Differences from the source:
--   - reading: bounded-error quantum query complexity of learning Majority (Definition 2.2) → queryComplexity: least T such that an oracle circuit over all unitary gates, with at most T plain, inverse or controlled calls to the Majority bit oracle, outputs the indicator bits of A on designated wires with probability at least 2/3 for every A of the promise; reason: Definition 2.2; p. 4: the bit and phase oracles are equivalent when applied in a controlled manner
--   - encoding: Q = Ω(log k) → ∃ c > 0 fixed before n and k; reason: the paper's O-convention; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 4.6, p. 50 (PDF p. 51)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity

namespace QuantumLTF.Membership.Supplement

/-- **Theorem 4.6 (Lower bound under the promise `1 ≤ |A| ≤ k`).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 4.6, p. 50
(PDF p. 51): "For every `n ≥ k ≥ 2`, `Q = Ω(log k)`."

**Formalization Note.** `Ω(log k)`: a constant `c > 0` fixed before `n, k`. `Q` is
`queryComplexity` (Definition 2.2) for the promise `1 ≤ |A| ≤ k`. -/
theorem theorem_4_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      c * Real.log k ≤ queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) := by sorry

end QuantumLTF.Membership.Supplement
