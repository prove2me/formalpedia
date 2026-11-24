-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_A_1
-- name    : QuantumLTF.Membership.Supplement.theorem_A_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T10:51:02.135208+00:00
-- url     : https://prove2.me/theorems/5935984f-6a36-4401-9199-c7a30f30fecc
-- title:
--   Theorem A.1 — classical upper bound $O(k\log(en/k))$ for learning Majority
-- statement:
--   1. There is a constant $C>0$ such that for all $n\ge k\ge1$ there is a deterministic adaptive classical algorithm making at most
--   $$C\,k\log\frac{en}{k}$$
--   membership queries at points of $\{-1,1\}^n$ which outputs $A$ exactly for every hidden set with $1\le|A|\le k$.
--   2. If $n=n(k)$ satisfies $\liminf_{k\to\infty}n(k)/k>1$, there are $C'$ and $k_0$ such that for every $k\ge k_0$ the same holds with $C'k\log(n(k)/k)$ queries.
--
--   This matches the classical lower bound $\Omega(k\log(n/k))$ and contrasts with the quantum $\Theta(\log k)$ of Theorem 4.1.
--
--   **Formalization Note** The algorithm is a query tree that queries only Boolean points; its depth is the worst-case number of queries. $\log$ is natural.
--
--   Differences from the source:
--   - reading: learned classically using … membership queries → a deterministic adaptive query tree (base QueryTree) that queries only points of {−1,1}ⁿ (IsBooleanTree), with depth bounded as stated, outputting A exactly for every A of the promise; reason: the proof's algorithm (binary search and adaptive group testing) is deterministic and exact
--   - reading: lim inf_{k→∞} n/k > 1 → n = n(k) a sequence with ∃ ρ > 1, eventually ρ ≤ n(k)/k; C' and k₀ may depend on the sequence; reason: equal to the liminf condition in the extended reals; Mathlib's real liminf is a junk value for unbounded sequences
--   - encoding: O(k log(en/k)), O(k log(n/k)) → ∃ C > 0 before n and k; e = exp 1; reason: the paper's O-convention; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem A.1, p. 86 (PDF p. 87)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_QueryTree
import Definitions.Def_QuantumLTF_Membership_Supplement_majJunta
import Definitions.Def_QuantumLTF_Membership_Supplement_IsBooleanTree

namespace QuantumLTF.Membership.Supplement

open QuantumLTF.Membership Filter

/-- **Theorem A.1 (Classical upper bound).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem A.1, p. 86 (PDF p. 87): "The
Majority-junta problem with the promise `1 ≤ |A| ≤ k` can be learned classically using
`O(k log(en/k))` membership queries for all `n ≥ k`. If `lim inf_{k→∞} n/k > 1`, this gives the
matching `O(k log(n/k))` classical upper bound."

**Formalization Note.** Both sentences. A classical learner is a deterministic adaptive query tree
(`QueryTree`) that queries only points of `{−1,1}ⁿ` (`IsBooleanTree`); the point `x` is the set
`S = {i : x_i = 1}` and the answer is `f_A(S)` (`majJunta`); depth is the worst-case number of queries,
and learning means outputting `A` exactly for every `A` of the promise (the proof's algorithm is
deterministic and exact). `O(·)`: a constant fixed before `n, k`; `log` natural, `e = exp 1`. Second
sentence: `n = n(k)` is a sequence; `lim inf_{k→∞} n(k)/k > 1` is written `∃ ρ > 1` with `ρ ≤ n(k)/k`
eventually (the same condition in the extended reals; Mathlib's real `liminf` would be the junk `0` for
an unbounded sequence); the constant `C'` and threshold `k₀` may depend on the sequence. -/
theorem theorem_A_1 :
    (∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      ∃ t : QueryTree n (Finset (Fin n)), IsBooleanTree t ∧
        (t.depth : ℝ) ≤ C * k * Real.log (Real.exp 1 * n / k) ∧
        ∀ A : Finset (Fin n), 1 ≤ A.card → A.card ≤ k →
          open Classical in
          t.run (fun x => majJunta A (Finset.univ.filter fun i => x i = 1)) = A) ∧
    ∀ nk : ℕ → ℕ, (∃ ρ : ℝ, 1 < ρ ∧ ∀ᶠ k in atTop, ρ ≤ (nk k : ℝ) / k) →
      ∃ C' : ℝ, 0 < C' ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∃ t : QueryTree (nk k) (Finset (Fin (nk k))), IsBooleanTree t ∧
          (t.depth : ℝ) ≤ C' * k * Real.log ((nk k : ℝ) / k) ∧
          ∀ A : Finset (Fin (nk k)), 1 ≤ A.card → A.card ≤ k →
            open Classical in
            t.run (fun x => majJunta A (Finset.univ.filter fun i => x i = 1)) = A := by sorry

end QuantumLTF.Membership.Supplement
