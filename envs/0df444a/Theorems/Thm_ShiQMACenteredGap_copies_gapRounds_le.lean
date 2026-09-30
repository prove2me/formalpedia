-- Prove2me | Theorems.Thm_ShiQMACenteredGap_copies_gapRounds_le
-- name    : ShiQMACenteredGap.copies_gapRounds_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T07:31:10.486355+00:00
-- url     : https://prove2.me/theorems/3217fc79-f903-4c3d-b42a-c541fd199c80
-- title:
--   Centered-gap normalization uses polynomially many copies
-- statement:
--   For every positive natural $q$, the number of witness copies needed by the centered-gap normalization schedule is bounded by $3^{3(\lfloor\log_2q\rfloor+1)}\le27q^5$. This gives an explicit polynomial resource bound.
-- source:
--   Yueheng Shi, AMPUNI-centered-gap.lean, formal bias analysis for copy-based QMA amplification; context: Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.copies_gapRounds_le (q : Nat) (hq : 0 < q) :
    3 ^ gapRounds q ≤ 27 * q ^ 5 := by sorry
