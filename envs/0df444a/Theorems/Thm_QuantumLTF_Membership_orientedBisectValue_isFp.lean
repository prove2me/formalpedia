-- Prove2me | Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_isFp
-- name    : QuantumLTF.Membership.orientedBisectValue_isFp
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:42:35.650708+00:00
-- url     : https://prove2.me/theorems/d946f94d-e1a2-4243-b8d9-132fc092570b
-- title:
--   Fixed-point propagation through orientation-aware bisection
-- statement:
--   If both endpoints of an interval share a signed fixed-point format with $B$ total bits and $f$ fractional bits, then the output after $q$ orientation-aware bisection updates has an exact format with $B+q+1$ total bits and $f+q+1$ fractional bits.
-- source:
--   Fixed-point invariant for Theorem 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_IsFp

theorem QuantumLTF.Membership.orientedBisectValue_isFp
    (s : ℤ) (q B f : ℕ) (lo hi h : ℝ)
    (hlo : IsFp B f lo) (hhi : IsFp B f hi) :
    IsFp (B + q + 1) (f + q + 1)
      (orientedBisectValue s q lo hi h) := by sorry
