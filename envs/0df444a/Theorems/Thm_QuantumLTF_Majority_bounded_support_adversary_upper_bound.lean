-- Prove2me | Theorems.Thm_QuantumLTF_Majority_bounded_support_adversary_upper_bound
-- name    : QuantumLTF.Majority.bounded_support_adversary_upper_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:14:12.249359+00:00
-- url     : https://prove2.me/theorems/4efc10ab-003d-477e-b125-0b5438b1ea43
-- title:
--   Adversary-to-algorithm upper bound for bounded Majority supports
-- statement:
--   Assume that for every $2\le k\le n$, the bounded-support Majority learning relation has a feasible dual adversary solution of cost at most $C_0\log k$, with one universal constant $C_0>0$. Then there is a universal constant $C>0$ and a bounded-error quantum learner which identifies every nonempty hidden support $A\subseteq[n]$ with $|A|\le k$, succeeds with probability at least $2/3$, and makes at most
--
--   $$
--   C\log k
--   $$
--
--   queries to the coherent Majority oracle.
--
--   This is the bounded-support specialization of the general dual-adversary/state-conversion upper bound. Arbitrary finite-dimensional inter-query unitaries may be decomposed exactly into one- and two-qubit unitaries, so restricting the circuit to the gate set used by the mission does not affect query complexity.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Sections 4.2–4.3, especially the feasible adversary solution and the transducer construction around Eqs. (129)–(132), leading to Theorem 4.5; general adversary/state-conversion upper-bound theorem cited there.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem bounded_support_adversary_upper_bound : ∀ C₀ : ℝ, 0 < C₀ → (∀ n k : ℕ, 2 ≤ k → k ≤ n → ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X ∧ DualCostAtMost X (C₀ * Real.log k)) → ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m), (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧ LearnsUpTo (k:=k) c out (2/3) := by sorry

end QuantumLTF.Majority
