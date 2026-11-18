-- Prove2me | Theorems.Thm_QuantumLTF_Majority_odd_separated_krawtchouk_witness
-- name    : QuantumLTF.Majority.odd_separated_krawtchouk_witness
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T15:42:55.685742+00:00
-- url     : https://prove2.me/theorems/193ad31b-c5f7-44c4-b483-28ce964e98f1
-- title:
--   Odd-size separated Krawtchouk witness with logarithmic energy
-- statement:
--   For every odd support size $r\ge3$, the degree-$(r-1)/2$ root-partition construction supplies lower- and upper-threshold Krawtchouk transforms $L$ and $U$. Their same-side distinguishing moments vanish, both mixed moments equal $1/2$, and the diagonal energy of $L+U$ is at most $C\log r$ for a universal constant $C$.
--
--   This combines the correctly stated feasibility content of Lemma 4.1 with the objective estimate of Lemmas 4.2–4.3, without discarding the transform-support information needed by the proof.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2, Lemmas 4.1–4.3 and equations (108)–(116).

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem odd_separated_krawtchouk_witness : ∃ C : ℝ, 0 < C ∧ ∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r → ∃ L U : Fin (r+1) → ℝ, (∀ A B : ExactSupports n r, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * L (intersectionIndex A S) * L (intersectionIndex B S) else 0) = 0) ∧ (∀ A B : ExactSupports n r, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * U (intersectionIndex A S) * U (intersectionIndex B S) else 0) = 0) ∧ (∀ A B : ExactSupports n r, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * L (intersectionIndex A S) * U (intersectionIndex B S) else 0) = 1/2) ∧ (∀ A B : ExactSupports n r, A ≠ B → (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then (2:ℝ)^(-n:ℤ) * U (intersectionIndex A S) * L (intersectionIndex B S) else 0) = 1/2) ∧ (∀ A : ExactSupports n r, ∑ S : Qubits n, (2:ℝ)^(-n:ℤ) * (L (intersectionIndex A S) + U (intersectionIndex A S))^2 ≤ C * Real.log r) := by sorry

end QuantumLTF.Majority
