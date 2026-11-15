-- Prove2me | Theorems.Thm_QuantumLTF_Majority_theorem_4_5
-- name    : QuantumLTF.Majority.theorem_4_5
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-14T17:48:50.785198+00:00
-- url     : https://prove2.me/theorems/1888e157-05bb-406d-84f0-953c0b0faf4a
-- title:
--   Theorem 4.5 — learning a hidden Majority support with $O(\log k)$ quantum queries
-- statement:
--   Let $2\le k\le n$. There is a bounded-error quantum algorithm which, for every unknown nonempty set $A\subseteq[n]$ with $|A|\le k$, identifies $A$ exactly using
--
--   $$
--   O(\log k)
--   $$
--
--   queries to the coherent Boolean membership oracle for $\operatorname{MAJORITY}_{|A|}(x_A)$. The same circuit is chosen before the hidden support $A$, and succeeds with probability at least $2/3$. In particular, the result includes the promise $|A|=k$; the case $k=1$ has constant query complexity.
--
--   This is the exponential improvement over the previous $O(k^{1/4})$ upper bound.
--
--   **Formalization Note** The measured output is required to be the exact characteristic vector of $A$. The big-$O$ constant is universal and quantified before $n$ and $k$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Theorem 4.5, p. 49 (PDF p. 50); upper-bound proof in Sections 4.2–4.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

/-- **Theorem 4.5 (Upper bound for learning Majority).** For every `2 ≤ k ≤ n`, a bounded-error quantum algorithm identifies every hidden nonempty support `A ⊆ [n]` of size at most `k` using `O(log k)` coherent Majority queries. The circuit is fixed before `A`, and its measured output is the exact characteristic vector of `A`. -/
theorem theorem_4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m)
        (out : Fin n ↪ Fin m),
        (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
        ∀ A : Finset (Fin n), A.Nonempty → A.card ≤ k →
          probEvent (act (c.unitary fun _ => majorityOracle A) (zeroKet m))
            (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3 := by sorry

end QuantumLTF.Majority
