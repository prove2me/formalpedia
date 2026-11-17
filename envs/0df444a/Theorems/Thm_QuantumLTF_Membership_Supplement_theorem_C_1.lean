-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_C_1
-- name    : QuantumLTF.Membership.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:52:27.429956+00:00
-- url     : https://prove2.me/theorems/fff71a6a-c811-4f71-80a1-a34afa5faf7d
-- title:
--   Theorem C.1 — lower bound $Q=\Omega(1+\log\min\{k,n-k\})$ under the promise $|A|=k$
-- statement:
--   1. There is a universal constant $c>0$ such that for all $1\le k\le n-1$,
--   $$Q_n(|A|=k)\ge c\,\big(1+\log\min\{k,n-k\}\big).$$
--   2. In particular, there is $c'>0$ with $Q_n(|A|=k)\ge c'\log k$ whenever $n\ge2k$ and $k\ge2$.
--
--   $Q_n$ is the bounded-error quantum query complexity of learning the Majority junta (Definition 2.2). With Theorem 4.5 this gives part (i) of Theorem 4.1.
--
--   Differences from the source:
--   - reading: bounded-error quantum query complexity of learning Majority (Definition 2.2) → queryComplexity: least T such that an oracle circuit over all unitary gates, with at most T plain, inverse or controlled calls to the Majority bit oracle, outputs the indicator bits of A on designated wires with probability at least 2/3 for every A of the promise; reason: Definition 2.2; p. 4: the bit and phase oracles are equivalent when applied in a controlled manner
--   - encoding: 1 ≤ k ≤ n − 1; Ω(·) in both sentences → k + 1 ≤ n (no natural-number subtraction at the boundary); one constant per sentence fixed before n and k; reason: the paper's O-convention; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem C.1, p. 95 (PDF p. 96)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity

namespace QuantumLTF.Membership.Supplement

/-- **Theorem C.1 (Lower bound under the promise `|A| = k`).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem C.1, p. 95 (PDF p. 96):
"Under the promise `|A| = k`, and `1 ≤ k ≤ n − 1`, `Q = Ω(1 + log(min{k, n − k}))`. In particular,
if `n ≥ 2k` and `k ≥ 2`, then `Q = Ω(log k)`."

**Formalization Note.** Both sentences, each with its own constant fixed before `n, k`.
`k ≤ n − 1` is written `k + 1 ≤ n`, so the natural-number subtraction `n − k ≥ 1` is exact. `Q` is
`queryComplexity` (Definition 2.2) for the promise `|A| = k`. -/
theorem theorem_C_1 :
    (∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k + 1 ≤ n →
      c * (1 + Real.log (min k (n - k) : ℕ)) ≤ queryComplexity n (fun A => A.card = k)) ∧
    (∃ c' : ℝ, 0 < c' ∧ ∀ n k : ℕ, 2 ≤ k → 2 * k ≤ n →
      c' * Real.log k ≤ queryComplexity n (fun A => A.card = k)) := by sorry

end QuantumLTF.Membership.Supplement
