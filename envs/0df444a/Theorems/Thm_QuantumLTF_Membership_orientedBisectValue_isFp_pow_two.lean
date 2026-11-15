-- Prove2me | Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_isFp_pow_two
-- name    : QuantumLTF.Membership.orientedBisectValue_isFp_pow_two
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:33:49.434743+00:00
-- url     : https://prove2.me/theorems/074379a9-7bc0-44ca-b6e2-5d7df65fee44
-- title:
--   Dyadic fixed-point form of the bisection output
-- statement:
--   Starting from the symmetric dyadic interval $[-2^m,2^m]$, after $q$ bisection updates the returned midpoint is an exact signed fixed-point number with $q+1$ fractional bits and at most $m+q+2$ total bits. This is independent of which branches the sign tests select.
-- source:
--   Fixed-point component of Theorem 3.1 in Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_IsFp

theorem QuantumLTF.Membership.orientedBisectValue_isFp_pow_two
    (s : ℤ) (m q : ℕ) (h : ℝ) :
    IsFp (m + q + 2) (q + 1)
      (orientedBisectValue s q (-((2 : ℝ) ^ m)) ((2 : ℝ) ^ m) h) := by sorry
