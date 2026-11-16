-- Prove2me | Theorems.Thm_QuantumLTF_Majority_theorem_4_10
-- name    : QuantumLTF.Majority.theorem_4_10
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:41:18.631059+00:00
-- url     : https://prove2.me/theorems/ad7bcd15-54a4-4158-a288-5708c2f4798e
-- title:
--   Theorem 4.10 — gate-efficient learning with bounded support size
-- statement:
--   For nonempty hidden supports of size at most $k$, the learner uses $O(\log k)$ queries, $O(n\log n\log k)$ gates and depth $O(\log n\log k)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Theorem 4.10, p.56 (PDF p.57).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem theorem_4_10 : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m) (d : ℕ), LearnsUpTo (k:=k) c out (1-ε) ∧ (c.queryCount 0 : ℝ) ≤ C*Real.log k ∧ (c.gateCount : ℝ) ≤ C*n*Real.log (n+1)*Real.log k ∧ (d : ℝ) ≤ C*Real.log (n+1)*Real.log k := by sorry

end QuantumLTF.Majority
