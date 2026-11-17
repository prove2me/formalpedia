-- Prove2me | Theorems.Thm_QuantumLTF_Majority_intersection_rank_one_posSemidef
-- name    : QuantumLTF.Majority.intersection_rank_one_posSemidef
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:46:10.100755+00:00
-- url     : https://prove2.me/theorems/5b84e611-fe80-4c12-9c89-ab0ed4edf61f
-- title:
--   Positive semidefiniteness of intersection-transform Gram matrices
-- statement:
--   For a fixed Boolean query string $S$, the exact-support adversary matrix with entries
--
--   $$
--   2^{-n}W(|A\cap S|)W(|B\cap S|)
--   $$
--
--   is positive semidefinite. It is a nonnegative scalar multiple of the rank-one Gram matrix formed by the vector $A\mapsto W(|A\cap S|)$.
-- source:
--   Rank-one Gram-matrix observation in the exact-support adversary construction of Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem intersection_rank_one_posSemidef : ∀ n r : ℕ, ∀ W : Fin (r+1) → ℝ, ∀ S : Qubits n, Matrix.PosSemidef (fun A B : ExactSupports n r => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)) := by sorry

end QuantumLTF.Majority
