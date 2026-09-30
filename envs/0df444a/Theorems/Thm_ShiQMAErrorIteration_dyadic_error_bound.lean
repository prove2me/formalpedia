-- Prove2me | Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound
-- name    : ShiQMAErrorIteration.dyadic_error_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T06:25:41.919035+00:00
-- url     : https://prove2.me/theorems/484a2fd8-9761-41e2-8d49-6d0510c29aa4
-- title:
--   Three initial rounds yield dyadic QMA error decay
-- statement:
--   For the majority-of-three error recurrence starting at $1/3$, every natural number $r$ satisfies $e_{r+3}\le 2^{-2^r}$. Thus a logarithmic number of further rounds reaches any specified exponential error exponent.
-- source:
--   Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf; original Lean proof: Yueheng Shi, AMPUNI-error-iteration.lean

import Definitions.Def_ShiQMAErrorIteration
import Theorems.Thm_ShiQMAErrorIteration_scaled_error_bound

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.dyadic_error_bound (r : Nat) :
    error (r + 3) ≤ ((1 : ℝ) / 2) ^ (2 ^ r) := by sorry
