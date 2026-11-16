-- Prove2me | Theorems.Thm_QuantumLTF_Membership_rho_sqrt_le
-- name    : QuantumLTF.Membership.rho_sqrt_le
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T18:56:55.089217+00:00
-- url     : https://prove2.me/theorems/dc215288-290b-446b-853e-02b1b288691f
-- title:
--   The grid scale cancels the dimension factor
-- statement:
--   The dyadic scale ρ is at most the reciprocal of 40√n, so multiplying it by √n gives at most 1/40.
-- source:
--   Scale estimate used in Theorems 3.2 and 3.3 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_rho

theorem QuantumLTF.Membership.rho_sqrt_le (n : ℕ) (hn : 1 ≤ n) :
    rho n * Real.sqrt n ≤ 1 / 40 := by sorry
