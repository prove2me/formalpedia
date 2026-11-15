-- Prove2me | Theorems.Thm_QuantumLTF_Membership_IsFp_midpoint
-- name    : QuantumLTF.Membership.IsFp.midpoint
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:39:56.72121+00:00
-- url     : https://prove2.me/theorems/8886bdcc-7ef7-496b-bf4b-822fe5848c4d
-- title:
--   Fixed-point formats are closed under midpoints
-- statement:
--   The midpoint of two signed fixed-point numbers having $B$ total bits and $f$ fractional bits has an exact representation with $B+1$ total bits and $f+1$ fractional bits.
-- source:
--   Supporting arithmetic lemma for Theorem 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_IsFp

theorem QuantumLTF.Membership.IsFp.midpoint (B f : ℕ) (x y : ℝ)
    (hx : IsFp B f x) (hy : IsFp B f y) :
    IsFp (B + 1) (f + 1) ((x + y) / 2) := by sorry
