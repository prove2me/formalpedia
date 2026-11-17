-- Prove2me | Theorems.Thm_QuantumLTF_Majority_exact_support_dual_from_krawtchouk_witness
-- name    : QuantumLTF.Majority.exact_support_dual_from_krawtchouk_witness
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-17T00:36:26.512642+00:00
-- url     : https://prove2.me/theorems/98e92ce1-dd95-427d-b796-bc929c53f48a
-- title:
--   Exact-support dual solution from a Krawtchouk witness
-- statement:
--   Let $3\le r\le n$. Suppose $p_t,q_t$ satisfy the endpoint normalization and complementary-support conditions of the odd-support Krawtchouk construction, their weighted signed cross term is zero, and their binomial energy is at most $T$. Then the rank-one Gram matrices obtained from their intersection Krawtchouk transform form a feasible dual adversary solution for exact supports of size $r$, with objective at most $T$.
--
--   The proof combines feasibility of the intersection transform, corrected scalar Parseval, and counting Boolean query strings by their intersection size with a fixed support.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2: rank-one Krawtchouk adversary matrices, feasibility, and objective calculation leading to Lemmas 4.1–4.3.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem exact_support_dual_from_krawtchouk_witness : ∀ n r : ℕ, 3 ≤ r → r ≤ n → ∀ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 → (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) → (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 → ∀ T : ℝ, (∑ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2)) ≤ T → ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ, DualFeasible (fun A : ExactSupports n r => A.1) X ∧ DualCostAtMost X T := by sorry

end QuantumLTF.Majority
