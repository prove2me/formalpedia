-- Prove2me | Theorems.Thm_QuantumLTF_Membership_norm_gridVec_le
-- name    : QuantumLTF.Membership.norm_gridVec_le
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T18:54:00.147194+00:00
-- url     : https://prove2.me/theorems/9dfacebd-fde0-41f6-a2a5-1e6e871ee7c7
-- title:
--   Norm bound for the centered product grid
-- statement:
--   Every n-dimensional centered grid point has Euclidean norm at most √n/2 because each coordinate lies in [-1/2,1/2].
-- source:
--   Centered-grid norm estimate used in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_gridVec
open QAlgorithms

theorem QuantumLTF.Membership.norm_gridVec_le (n b : ℕ) (x : Fin n → Qubits b) :
    ‖gridVec n b x‖ ≤ Real.sqrt n / 2 := by sorry
