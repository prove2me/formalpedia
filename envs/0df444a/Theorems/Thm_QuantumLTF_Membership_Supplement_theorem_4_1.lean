-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_1
-- name    : QuantumLTF.Membership.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:43:24.999206+00:00
-- url     : https://prove2.me/theorems/469e5d0b-e77f-4076-bbb4-165a871e3398
-- title:
--   Theorem 4.1 — quantum query complexity of learning Majority is $\Theta(\log k)$
-- statement:
--   There are universal constants $c,C>0$ such that for every $k\ge2$:
--
--   1. under the promise $|A|=k$, for every $n\ge2k$: $\;c\log k\le Q_n(|A|=k)\le C\log k$;
--   2. under the promise $1\le|A|\le k$, for every $n\ge k$: $\;c\log k\le Q_n(1\le|A|\le k)\le C\log k$.
--
--   Here $Q_n(\mathcal A)$ is the bounded-error quantum query complexity of learning the Majority junta $f_A$ (Definition 2.2). The theorem is an exponential improvement over the previous $O(k^{1/4})$ upper bound of Belovs and closes the problem.
--
--   **Formalization Note** $\log$ is natural. The same constants serve both promises.
--
--   Differences from the source:
--   - reading: bounded-error quantum query complexity of learning Majority (Definition 2.2) → queryComplexity: least T such that an oracle circuit over all unitary gates, with at most T plain, inverse or controlled calls to the Majority bit oracle, outputs the indicator bits of A on designated wires with probability at least 2/3 for every A of the promise; reason: Definition 2.2; p. 4: the bit and phase oracles are equivalent when applied in a controlled manner
--   - encoding: Θ(log k) → ∃ c, C > 0 fixed before k and n, the same for both promises; reason: the paper's O-convention
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 4.1, p. 39 (PDF p. 40)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity

namespace QuantumLTF.Membership.Supplement

/-- **Theorem 4.1 (Query complexity of learning Majority).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 4.1, p. 39 (PDF p. 40):
"Let `k ≥ 2`. Under one of the following two promises (i) `|A| = k`, for every `n ≥ 2k`
(ii) `1 ≤ |A| ≤ k`, for every `n ≥ k` the bounded-error quantum query complexity of learning Majority
is `Θ(log k)`."

**Formalization Note.** `Q_n(𝒜)` is `queryComplexity` (Definition 2.2: error probability `≤ 1/3`,
Boolean membership oracle of the Majority junta, controlled calls allowed, any gates). `Θ(log k)` is
read with universal constants `c, C > 0` fixed before `k` and `n`, the same for both promises;
`log` is natural (`k ≥ 2`, so `log k > 0`). -/
theorem theorem_4_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (∀ n : ℕ, 2 * k ≤ n →
        c * Real.log k ≤ queryComplexity n (fun A => A.card = k) ∧
        (queryComplexity n (fun A => A.card = k) : ℝ) ≤ C * Real.log k) ∧
      (∀ n : ℕ, k ≤ n →
        c * Real.log k ≤ queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) ∧
        (queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) : ℝ) ≤ C * Real.log k) := by sorry

end QuantumLTF.Membership.Supplement
