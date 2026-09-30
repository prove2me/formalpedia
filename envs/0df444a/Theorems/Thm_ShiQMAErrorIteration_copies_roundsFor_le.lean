-- Prove2me | Theorems.Thm_ShiQMAErrorIteration_copies_roundsFor_le
-- name    : ShiQMAErrorIteration.copies_roundsFor_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T06:59:19.448389+00:00
-- url     : https://prove2.me/theorems/e0041bdf-23e9-4efc-a12f-a6707b68a229
-- title:
--   The logarithmic majority schedule uses quadratically many copies
-- statement:
--   For every positive natural number $m$, the number of verifier copies in the logarithmic majority-of-three schedule is at most $81m^2$: $3^{R(m)}\le81m^2$. This supplies a concrete polynomial witness and circuit resource bound.
-- source:
--   Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf; original Lean proof: Yueheng Shi, AMPUNI-error-iteration.lean

import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false
open ShiQMAErrorIteration

theorem ShiQMAErrorIteration.copies_roundsFor_le (m : Nat) (hm : 0 < m) : 3 ^ roundsFor m ≤ 81 * m ^ 2 := by sorry
