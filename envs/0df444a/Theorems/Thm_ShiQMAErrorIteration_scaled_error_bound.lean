-- Prove2me | Theorems.Thm_ShiQMAErrorIteration_scaled_error_bound
-- name    : ShiQMAErrorIteration.scaled_error_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T06:11:50.30737+00:00
-- url     : https://prove2.me/theorems/21ddfe87-99c1-42cc-9e01-44acf3724f7c
-- title:
--   Scaled majority-of-three error decays doubly exponentially
-- statement:
--   Let $e_0=1/3$ and $e_{k+1}=3e_k^2-2e_k^3$. For every natural number $r$, the scaled error after $r+1$ rounds satisfies $3e_{r+1}\le (7/9)^{2^r}$. This gives a quantitative decay law for repeated majority-of-three amplification.
-- source:
--   Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf; original Lean proof: Yueheng Shi, AMPUNI-error-iteration.lean

import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.scaled_error_bound (r : Nat) :
    3 * error (r + 1) ≤ ((7 : ℝ) / 9) ^ (2 ^ r) := by sorry
