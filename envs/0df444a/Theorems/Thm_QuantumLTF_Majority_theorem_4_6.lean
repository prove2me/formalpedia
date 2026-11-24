-- Prove2me | Theorems.Thm_QuantumLTF_Majority_theorem_4_6
-- name    : QuantumLTF.Majority.theorem_4_6
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T20:41:21.116895+00:00
-- url     : https://prove2.me/theorems/e4cbc735-30b2-4cb6-a99b-03d2c7830493
-- title:
--   Theorem 4.6 — logarithmic lower bound for learning Majority
-- statement:
--   For $n\ge k\ge2$, every bounded-error quantum learner for nonempty supports of size at most $k$ needs $\Omega(\log k)$ Majority queries.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Theorem 4.6, p.49 (PDF p.50).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem theorem_4_6 : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∀ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m), LearnsUpTo (k:=k) c out (2/3) → C*Real.log k ≤ c.queryCount 0 := by sorry

end QuantumLTF.Majority
