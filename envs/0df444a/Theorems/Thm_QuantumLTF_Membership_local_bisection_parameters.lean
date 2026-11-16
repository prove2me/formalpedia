-- Prove2me | Theorems.Thm_QuantumLTF_Membership_local_bisection_parameters
-- name    : QuantumLTF.Membership.local_bisection_parameters
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T19:07:38.500936+00:00
-- url     : https://prove2.me/theorems/160b0e78-6c63-4c68-bd11-7fa6720c3315
-- title:
--   Logarithmic parameters for localized bisection
-- statement:
--   For every target error below one eighth, a bisection count q can be chosen logarithmically in 1/η so that the localized binary-search error 2^(-q-2) is at most η.
-- source:
--   Query-count selection in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib

theorem QuantumLTF.Membership.local_bisection_parameters :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1 / 8 →
      ∃ q : ℕ, ((q : ℕ) : ℝ) ≤ C * Real.log (1 / η) ∧
        1 / (2 : ℝ) ^ (q + 2) ≤ η := by sorry
