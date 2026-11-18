-- Prove2me | Theorems.Thm_QuantumLTF_Majority_bounded_support_vector_coefficient_witness
-- name    : QuantumLTF.Majority.bounded_support_vector_coefficient_witness
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T16:55:53.989895+00:00
-- url     : https://prove2.me/theorems/9eb8ea72-3894-48d1-81a3-e623ddb8369e
-- title:
--   Joint vector witness with the coefficient-energy estimate
-- statement:
--   For all support sizes $1\le r\le k$ simultaneously, the vector-polynomial construction supplies vectors $W_{r,a}$ satisfying every within-size and cross-size adversary moment constraint. Their binomially weighted coefficient energy obeys
--
--   $$
--   2^{-r}\sum_{a=0}^{r}{r\choose a}\lVert W_{r,a}\rVert^2\le C\log k.
--   $$
--
--   This is the direct formal counterpart of the coupled construction in Lemma 4.4 and the coefficient estimate in Lemma 4.5, particularly equations (125)–(126).
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.3, Lemmas 4.4–4.5, equations (117)–(126).

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem bounded_support_vector_coefficient_witness : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∃ d : ℕ, ∃ W : ℕ → ℕ → Fin d → ℝ, (∀ A B : BoundedSupports n k, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, W A.1.card ((A.1.filter fun i => S i).card) j * W B.1.card ((B.1.filter fun i => S i).card) j else 0) = 1) ∧ (∀ r : ℕ, 1 ≤ r → r ≤ k → (1/(2:ℝ)^r) * ∑ a : Fin (r+1), (r.choose a : ℝ) * ∑ j : Fin d, (W r a j)^2 ≤ C * Real.log k) := by sorry

end QuantumLTF.Majority
