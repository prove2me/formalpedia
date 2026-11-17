-- Prove2me | Theorems.Thm_QuantumLTF_Majority_lemma_4_6
-- name    : QuantumLTF.Majority.lemma_4_6
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-16T11:00:00.002084+00:00
-- url     : https://prove2.me/theorems/66be7dcb-9975-4809-b5f5-331bb96118b3
-- title:
--   Lemma 4.6 — norm of the lower-bound adversary matrix
-- statement:
--   For the adversary matrix of Eq. (128) on the $m$-subsets of a known $2m$-element universe, $\|\Gamma\|=\sum_{s=1}^m1/s=\Theta(\log k)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Lemma 4.6, p.49 (PDF p.50).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem lemma_4_6 : ∀ {n m : ℕ} (U : Finset (Fin n)), U.card=2*m → specNorm (fun A B : {A : Finset (Fin n) // A⊆U ∧ A.card=m} => (lowerAdversary U A B : ℂ)) = ∑ s ∈ Finset.Icc 1 m, (1:ℝ)/s := by sorry

end QuantumLTF.Majority
