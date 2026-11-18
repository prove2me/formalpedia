-- Prove2me | Theorems.Thm_QuantumLTF_Majority_bounded_support_vector_moment_witness
-- name    : QuantumLTF.Majority.bounded_support_vector_moment_witness
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T16:45:28.91451+00:00
-- url     : https://prove2.me/theorems/37814a99-ccfb-4084-820d-47557148eac0
-- title:
--   Joint bounded-support vector witness with logarithmic energy
-- statement:
--   For every promise $1\le |A|\le k$, the coupled vector-polynomial construction of Section 4.3 provides vectors $W_{r,a}$ for all support sizes simultaneously. Their distinguishing Gram moments satisfy every dual adversary constraint, including cross-size pairs, and their maximum diagonal energy is bounded by $C\log k$.
--
--   Unlike an assembly of independent exact-size solutions, this theorem retains the correction coordinates $C_{m\ell}$ that enforce the cross-size constraints in equations (121)–(124).
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.3, Lemmas 4.4–4.5 and equations (117)–(126).

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem bounded_support_vector_moment_witness : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∃ d : ℕ, ∃ W : ℕ → ℕ → Fin d → ℝ, (∀ A B : BoundedSupports n k, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, W A.1.card ((A.1.filter fun i => S i).card) j * W B.1.card ((B.1.filter fun i => S i).card) j else 0) = 1) ∧ (∀ A : BoundedSupports n k, ∑ S : Qubits n, (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, (W A.1.card ((A.1.filter fun i => S i).card) j)^2 ≤ C * Real.log k) := by sorry

end QuantumLTF.Majority
