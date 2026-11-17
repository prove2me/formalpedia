-- Prove2me | Theorems.Thm_QuantumLTF_Majority_odd_exact_dual_log_cost
-- name    : QuantumLTF.Majority.odd_exact_dual_log_cost
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:19:04.020945+00:00
-- url     : https://prove2.me/theorems/9b85edb3-b232-472f-a8c4-28de6717150a
-- title:
--   Logarithmic adversary cost for odd exact support size
-- statement:
--   There is a universal constant $C>0$ such that, for every odd support size $3\le r\le n$, the exact-size Majority learning relation admits a feasible dual adversary solution of objective value at most
--
--   $$
--   C\log r.
--   $$
--
--   This is the odd-cardinality adversary construction obtained from the Krawtchouk polynomial families in Section 4.2. The corrected two-channel Parseval identity controls its diagonal objective.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Sections 4.2–4.3, odd-cardinality Krawtchouk adversary construction and logarithmic objective estimate.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem odd_exact_dual_log_cost : ∃ C : ℝ, 0 < C ∧ ∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r → ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ, DualFeasible (fun A : ExactSupports n r => A.1) X ∧ DualCostAtMost X (C * Real.log r) := by sorry

end QuantumLTF.Majority
