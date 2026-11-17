-- Prove2me | Theorems.Thm_QuantumLTF_Majority_odd_exact_to_bounded_dual_log_cost
-- name    : QuantumLTF.Majority.odd_exact_to_bounded_dual_log_cost
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:19:05.904609+00:00
-- url     : https://prove2.me/theorems/06920bf9-a2e2-45c2-a47a-07dc55768fd0
-- title:
--   Lift and assembly from odd exact supports to bounded supports
-- statement:
--   Suppose all odd exact support sizes admit dual adversary solutions of cost at most $C_0\log r$. Then a universal constant $C>0$ exists such that the full promise $1\le |A|\le k$ admits a feasible solution of cost at most
--
--   $$
--   C\log k.
--   $$
--
--   The construction applies the one-coordinate lift to even cardinalities, which changes resources only by a constant factor, and assembles the cardinality blocks using the auxiliary component of the Section 4.3 adversary vectors. The cases of support size one and two are absorbed into the universal constant.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Eq. (127) and Sections 4.3–4.3.1: lift for even sizes and bounded-support adversary assembly leading to Lemma 4.5.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem odd_exact_to_bounded_dual_log_cost : ∀ C₀ : ℝ, 0 < C₀ → (∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r → ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ, DualFeasible (fun A : ExactSupports n r => A.1) X ∧ DualCostAtMost X (C₀ * Real.log r)) → ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X ∧ DualCostAtMost X (C * Real.log k) := by sorry

end QuantumLTF.Majority
