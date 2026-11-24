-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_5
-- name    : QuantumLTF.Membership.Supplement.theorem_4_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T10:44:14.247203+00:00
-- url     : https://prove2.me/theorems/9563c5bf-1483-4801-9cd5-c11bcfb66036
-- title:
--   Theorem 4.5 — upper bound $Q=O(\log k)$ for learning Majority; constant for $k=1$
-- statement:
--   1. There is a universal constant $C>0$ such that for every $2\le k\le n$,
--   $$Q_n(1\le|A|\le k)\le C\log k\qquad\text{and}\qquad Q_n(|A|=k)\le C\log k .$$
--   2. The case $k=1$ has constant query complexity: there is a constant $C_1$ with $Q_n(|A|=1)\le C_1$ for every $n\ge1$.
--
--   $Q_n$ is the bounded-error quantum query complexity of learning the Majority junta (Definition 2.2).
--
--   Differences from the source:
--   - reading: bounded-error quantum query complexity of learning Majority (Definition 2.2) → queryComplexity: least T such that an oracle circuit over all unitary gates, with at most T plain, inverse or controlled calls to the Majority bit oracle, outputs the indicator bits of A on designated wires with probability at least 2/3 for every A of the promise; reason: Definition 2.2; p. 4: the bit and phase oracles are equivalent when applied in a controlled manner
--   - reading: The case k = 1 has constant query complexity → ∃ C₁ ∀ n ≥ 1, Q_n(|A| = 1) ≤ C₁; reason: for k = 1 both promises are |A| = 1
--   - encoding: Q = O(log k) → ∃ C > 0 fixed before k and n, for both promises; reason: the paper's O-convention; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 4.5, p. 49 (PDF p. 50)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity

namespace QuantumLTF.Membership.Supplement

/-- **Theorem 4.5 (Upper bound for learning Majority).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 4.5, p. 49 (PDF p. 50):
"For every `2 ≤ k ≤ n`, under the promises `1 ≤ |A| ≤ k` or `|A| = k`, `Q = O(log k)`. The case
`k = 1` has constant query complexity."

**Formalization Note.** Both sentences. `O(log k)`: a constant `C` fixed before `k, n`, for both
promises. "The case `k = 1`": the promise `1 ≤ |A| ≤ 1`, i.e. `|A| = 1`, has `Q_n ≤ C₁` for every
`n ≥ 1` with one constant `C₁`. `Q` is `queryComplexity` (Definition 2.2). -/
theorem theorem_4_5 :
    (∃ C : ℝ, 0 < C ∧ ∀ k n : ℕ, 2 ≤ k → k ≤ n →
      (queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) : ℝ) ≤ C * Real.log k ∧
      (queryComplexity n (fun A => A.card = k) : ℝ) ≤ C * Real.log k) ∧
    (∃ C₁ : ℕ, ∀ n : ℕ, 1 ≤ n → queryComplexity n (fun A => A.card = 1) ≤ C₁) := by sorry

end QuantumLTF.Membership.Supplement
