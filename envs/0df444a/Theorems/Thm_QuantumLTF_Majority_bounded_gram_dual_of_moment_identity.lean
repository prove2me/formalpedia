-- Prove2me | Theorems.Thm_QuantumLTF_Majority_bounded_gram_dual_of_moment_identity
-- name    : QuantumLTF.Majority.bounded_gram_dual_of_moment_identity
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T16:45:25.975799+00:00
-- url     : https://prove2.me/theorems/61156c74-d8ab-490a-8c6e-784f0fd87105
-- title:
--   Bounded-support Gram family from the adversary moment identity
-- statement:
--   Let $W_{r,a}$ be vectors indexed jointly by the hidden support size $r$ and intersection size $a$. If their normalized Gram moments equal one on every pair of distinct hidden supports after restricting to distinguishing queries, then the resulting family of Gram matrices is feasible for the dual adversary SDP.
--
--   This is the abstract positive-semidefinite/feasibility step for the vector-valued construction in Lemma 4.4.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.3, Lemma 4.4, equations (117)–(124).

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem bounded_gram_dual_of_moment_identity : ∀ n k d : ℕ, ∀ W : ℕ → ℕ → Fin d → ℝ, (∀ A B : BoundedSupports n k, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, W A.1.card ((A.1.filter fun i => S i).card) j * W B.1.card ((B.1.filter fun i => S i).card) j else 0) = 1) → let X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ := fun S A B => (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, W A.1.card ((A.1.filter fun i => S i).card) j * W B.1.card ((B.1.filter fun i => S i).card) j; DualFeasible (fun A : BoundedSupports n k => A.1) X := by sorry

end QuantumLTF.Majority
