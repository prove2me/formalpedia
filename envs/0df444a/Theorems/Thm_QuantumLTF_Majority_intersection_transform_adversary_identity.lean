-- Prove2me | Theorems.Thm_QuantumLTF_Majority_intersection_transform_adversary_identity
-- name    : QuantumLTF.Majority.intersection_transform_adversary_identity
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:46:10.669473+00:00
-- url     : https://prove2.me/theorems/4eb5ee99-0db6-42c8-ae65-5e3d1c132a5a
-- title:
--   Adversary feasibility identity for the intersection transform
-- statement:
--   For two distinct exact supports $A,B$ of size $r$, the intersection-transform Gram matrices satisfy the dual adversary constraint
--
--   $$
--   \sum_{S:\,f_A(S)\ne f_B(S)}X_S[A,B]=1.
--   $$
--
--   The endpoint normalization fixes the value to one, while the complementary zero sets of the two Krawtchouk coefficient families cancel all other Fourier components. This is the nontrivial feasibility calculation in Lemma 4.1.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2, feasibility calculation for the intersection/Krawtchouk adversary matrices, formalized as Lemma 4.1.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem intersection_transform_adversary_identity : ∀ n r : ℕ, 1 ≤ r → r ≤ n → ∀ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 → (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) → let W := intersectionTransform r p q; let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ := fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S); ∀ A B, A ≠ B → ∑ S : Qubits n, (if majorityBit A.1 S ≠ majorityBit B.1 S then X S A B else 0) = 1 := by sorry

end QuantumLTF.Majority
