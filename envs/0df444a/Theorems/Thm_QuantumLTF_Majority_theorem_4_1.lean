-- Prove2me | Theorems.Thm_QuantumLTF_Majority_theorem_4_1
-- name    : QuantumLTF.Majority.theorem_4_1
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-16T10:58:38.055964+00:00
-- url     : https://prove2.me/theorems/5c970024-0c65-4552-8359-fa0a4f4d85f0
-- title:
--   Theorem 4.1 — query complexity of learning Majority
-- statement:
--   For every $k\ge2$, learning a hidden Majority support has bounded-error quantum query complexity $\Theta(\log k)$ under both promises $|A|=k,n\ge2k$ and $1\le|A|\le k,n\ge k$.
-- source:
--   Krivcenko, Nguyen, de Wolf, STOC 2027 submission #347, Theorem 4.1, p.39 (PDF p.40).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem theorem_4_1 : ∃ Cu Cl : ℝ, 0 < Cu ∧ 0 < Cl ∧ ∀ k : ℕ, 2 ≤ k → ((∀ n : ℕ, 2*k ≤ n → (∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m), (c.queryCount 0 : ℝ) ≤ Cu*Real.log k ∧ LearnsExact (k:=k) c out (2/3)) ∧ ∀ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m), LearnsExact (k:=k) c out (2/3) → Cl*Real.log k ≤ c.queryCount 0) ∧ (∀ n : ℕ, k ≤ n → (∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m), (c.queryCount 0 : ℝ) ≤ Cu*Real.log k ∧ LearnsUpTo (k:=k) c out (2/3)) ∧ ∀ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m), LearnsUpTo (k:=k) c out (2/3) → Cl*Real.log k ≤ c.queryCount 0)) := by sorry

end QuantumLTF.Majority
