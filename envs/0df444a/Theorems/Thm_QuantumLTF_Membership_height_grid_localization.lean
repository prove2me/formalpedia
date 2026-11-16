-- Prove2me | Theorems.Thm_QuantumLTF_Membership_height_grid_localization
-- name    : QuantumLTF.Membership.height_grid_localization
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T18:59:37.442393+00:00
-- url     : https://prove2.me/theorems/b6b9d8c6-ce69-4b39-8426-406f18863021
-- title:
--   Scaled-grid heights stay near the estimated offset
-- statement:
--   Under the reference-direction event and an ε/100 estimate of the offset, every boundary height on the scaled centered grid lies within one quarter of that estimate.
-- source:
--   Search-interval localization in the proof of Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
open QAlgorithms

theorem QuantumLTF.Membership.height_grid_localization {n b : ℕ}
    (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w p : EuclideanSpace ℝ (Fin n)) (θ htil : ℝ)
    (hw : ‖w‖ = 1) (ha : 1 / 10 ≤ |inner ℝ w p|)
    (hhtil : |htil - height w θ p 0| ≤ ε / 100)
    (x : Fin n → Qubits b) :
    |height w θ p (rho n • gridVec n b x) - htil| ≤ 1 / 4 := by sorry
