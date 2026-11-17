-- Prove2me | Theorems.Thm_QuantumLTF_Majority_compile_bounded_support_dual
-- name    : QuantumLTF.Majority.compile_bounded_support_dual
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:23:37.428202+00:00
-- url     : https://prove2.me/theorems/e11299ba-8050-4e16-b40e-d0af510afe88
-- title:
--   Compile a bounded-support dual solution into a quantum learner
-- statement:
--   There is a universal constant $K>0$ with the following property. Given a feasible dual adversary solution of cost at most $T\ge0$ for learning a nonempty hidden Majority support of size at most $k$, one can construct a quantum learner that succeeds with probability at least $2/3$ and uses at most
--
--   $$
--   K(T+1)
--   $$
--
--   queries.
--
--   This is the finite bounded-support specialization of the general adversary/state-conversion upper bound. The additive constant handles dual costs below one. Inter-query unitaries can be decomposed into the mission’s arbitrary one- and two-qubit unitary gate set without increasing query count.
-- source:
--   General adversary bound/state-conversion upper bound specialized to the finite Majority-support identification relation; Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.4, Eqs. (129)–(132), and the cited transducer/adversary conversion theorem.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem compile_bounded_support_dual : ∃ K : ℝ, 0 < K ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∀ T : ℝ, 0 ≤ T → ∀ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X → DualCostAtMost X T → ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m), (c.queryCount 0 : ℝ) ≤ K * (T + 1) ∧ LearnsUpTo (k:=k) c out (2/3) := by sorry

end QuantumLTF.Majority
