-- Prove2me | Theorems.Thm_ShiQMAErrorIteration_error_roundsFor
-- name    : ShiQMAErrorIteration.error_roundsFor
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T06:42:35.827995+00:00
-- url     : https://prove2.me/theorems/0be0f341-5a49-4922-8e32-9626aab07e93
-- title:
--   A logarithmic majority schedule meets any dyadic error target
-- statement:
--   Define the number of majority-of-three rounds by $R(m)=\lfloor\log_2m\rfloor+4$. For every natural target exponent $m$, the resulting error is at most $2^{-m}$, including the small cases $m=0$ and $m=1$.
-- source:
--   Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf; original Lean proof: Yueheng Shi, AMPUNI-error-iteration.lean

import Definitions.Def_ShiQMAErrorIteration
import Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.error_roundsFor (m : Nat) : error (roundsFor m) ≤ ((1 : ℝ) / 2) ^ m := by sorry
