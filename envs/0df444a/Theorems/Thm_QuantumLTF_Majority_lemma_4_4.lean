-- Prove2me | Theorems.Thm_QuantumLTF_Majority_lemma_4_4
-- name    : QuantumLTF.Majority.lemma_4_4
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-16T11:01:04.061167+00:00
-- url     : https://prove2.me/theorems/77bbcdeb-23e5-4bc3-b19d-50b322c9ed3b
-- title:
--   Lemma 4.4 — feasibility for bounded support
-- statement:
--   The vector-valued construction, including the even-cardinality lift, is feasible for all nonempty supports of size at most $k$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Lemma 4.4, p.46.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

namespace QuantumLTF.Majority

open QAlgorithms

theorem lemma_4_4 : ∀ n k : ℕ, 1≤k → k≤n → ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X := by sorry

end QuantumLTF.Majority
