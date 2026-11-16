-- Prove2me | Theorems.Thm_QuantumLTF_Membership_height_rho_grid_affine
-- name    : QuantumLTF.Membership.height_rho_grid_affine
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:24:24.800188+00:00
-- url     : https://prove2.me/theorems/a9f9e79a-2fc2-497f-a533-20376aa456fc
-- title:
--   Height on the scaled centered grid
-- statement:
--   On the scaled centered grid used by the height oracle, the boundary height equals its offset at zero minus the grid directional inner product multiplied by ρ and divided by the reference coefficient.
-- source:
--   Affine-grid identity used in Theorems 3.2 and 3.3 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
open QAlgorithms

theorem QuantumLTF.Membership.height_rho_grid_affine {n b : ℕ}
    (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (x : Fin n → Qubits b)
    (ha : inner ℝ w p ≠ 0) :
    height w θ p (rho n • gridVec n b x) =
      height w θ p 0 - rho n * inner ℝ w (gridVec n b x) / inner ℝ w p := by sorry
