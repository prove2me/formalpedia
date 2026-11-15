-- Prove2me | Theorems.Thm_QuantumLTF_Membership_dyadic_bisection_parameters
-- name    : QuantumLTF.Membership.dyadic_bisection_parameters
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:53:33.922763+00:00
-- url     : https://prove2.me/theorems/8b1afb3d-b16e-452d-84aa-793bfd343cad
-- title:
--   Uniform logarithmic bounds for dyadic bisection
-- statement:
--   For every positive dyadic exponent m and target error between zero and one, a bisection count q can be chosen so that the error is at most ζ and both the query count and fixed-point bit count are bounded by one universal constant times log(2^m/ζ).
-- source:
--   Quantitative binary-search estimate used in Theorem 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib

theorem QuantumLTF.Membership.dyadic_bisection_parameters :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ q : ℕ,
        ((q + 2 : ℕ) : ℝ) ≤ C * Real.log ((2 : ℝ) ^ m / ζ) ∧
        ((m + q + 2 : ℕ) : ℝ) ≤ C * Real.log ((2 : ℝ) ^ m / ζ) ∧
        2 * (2 : ℝ) ^ m / (2 : ℝ) ^ (q + 1) ≤ ζ := by sorry
