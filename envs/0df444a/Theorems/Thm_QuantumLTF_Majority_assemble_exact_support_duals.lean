-- Prove2me | Theorems.Thm_QuantumLTF_Majority_assemble_exact_support_duals
-- name    : QuantumLTF.Majority.assemble_exact_support_duals
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:53:49.451249+00:00
-- url     : https://prove2.me/theorems/9cce03a0-fdb6-4d7d-9511-d5f744d04f2f
-- title:
--   Assemble exact-cardinality dual solutions for the bounded-support promise
-- statement:
--   Suppose that, uniformly for every cardinality $1\le r\le k$, the exact-size Majority relation has a feasible dual solution of cost at most $C_0\log k$. Then the full bounded-support relation $1\le|A|\le k$ has a feasible dual solution of cost at most $C\log k$ for a universal constant $C$.
--
--   The construction is the Section 4.3 direct-sum/auxiliary-component assembly. Its cross-cardinality components enforce the adversary constraints between supports of different sizes without summing the costs over all $r$.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Sections 4.3–4.3.1, bounded-support adversary vectors and their auxiliary component, leading to Lemma 4.5.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem assemble_exact_support_duals : ∀ C₀ : ℝ, 0 < C₀ → (∀ n k r : ℕ, 2 ≤ k → k ≤ n → 1 ≤ r → r ≤ k → ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ, DualFeasible (fun A : ExactSupports n r => A.1) X ∧ DualCostAtMost X (C₀ * Real.log k)) → ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X ∧ DualCostAtMost X (C * Real.log k) := by sorry

end QuantumLTF.Majority
