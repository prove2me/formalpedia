-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_bounds
-- name    : ShiQMACenteredGap.biasIter_bounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T08:35:23.008279+00:00
-- url     : https://prove2.me/theorems/b4018cc4-e31d-436a-9c98-8033ab589a60
-- title:
--   Centered majority iteration preserves the bias interval
-- statement:
--   If an initial centered acceptance bias is between $0$ and $1/2$, then every number of majority-of-three iterations leaves the bias in the same interval.
-- source:
--   Yueheng Shi, AMPUNI-centered-gap.lean, lines 22–68; context: Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.biasIter_bounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    0 ≤ biasIter d r ∧ biasIter d r ≤ 1 / 2 := by sorry
