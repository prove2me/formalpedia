-- Prove2me | Theorems.Thm_QuantumLTF_Majority_lemma_4_1
-- name    : QuantumLTF.Majority.lemma_4_1
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-16T11:01:13.697751+00:00
-- url     : https://prove2.me/theorems/a2b9d14c-e114-464b-8ca7-d50a2f33867d
-- title:
--   Lemma 4.1 — feasibility of the intersection-free construction
-- statement:
--   The partitioned-root Krawtchouk construction is feasible for every $n\ge k$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Lemma 4.1, p.41.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem lemma_4_1 : ∀ n k : ℕ, 1≤k → k≤n → ∀ p q : Fin (k+1) → ℝ, p 0*q 0=1/2 → (∀ t : Fin (k+1), 1≤t.1 → t.1<k → (p t=0 ↔ q t≠0)) → let W:=intersectionTransform k p q; let X : Qubits n → Matrix (ExactSupports n k) (ExactSupports n k) ℝ := fun S A B => (2:ℝ)^(-n:ℤ)*W (intersectionIndex A S)*W (intersectionIndex B S); DualFeasible (fun A : ExactSupports n k => A.1) X := by sorry

end QuantumLTF.Majority
