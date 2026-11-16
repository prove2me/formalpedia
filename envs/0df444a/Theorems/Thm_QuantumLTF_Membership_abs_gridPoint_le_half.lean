-- Prove2me | Theorems.Thm_QuantumLTF_Membership_abs_gridPoint_le_half
-- name    : QuantumLTF.Membership.abs_gridPoint_le_half
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:49:27.180355+00:00
-- url     : https://prove2.me/theorems/ea1d52f6-3d4f-49af-ae66-ccee91377f65
-- title:
--   Centered grid points lie in the half interval
-- statement:
--   Every point of the centered b-bit grid lies in the interval [-1/2,1/2].
-- source:
--   Centered grid bounds used in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
open QAlgorithms

theorem QuantumLTF.Membership.abs_gridPoint_le_half (b : ℕ) (z : Qubits b) :
    |gridPoint b z| ≤ 1 / 2 := by sorry
