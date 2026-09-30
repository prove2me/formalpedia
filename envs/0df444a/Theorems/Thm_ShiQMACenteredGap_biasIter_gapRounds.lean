-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_gapRounds
-- name    : ShiQMACenteredGap.biasIter_gapRounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T07:14:21.17205+00:00
-- url     : https://prove2.me/theorems/5c840c0c-66e9-4129-ab89-a158d6b82d45
-- title:
--   A logarithmic schedule turns an inverse-polynomial bias into a constant
-- statement:
--   Suppose $0\le d\le1/2$ and $qd\ge1/6$ for a natural number $q$. After $3(\lfloor\log_2q\rfloor+1)$ majority-of-three rounds, the iterated centered bias is at least $1/6$.
-- source:
--   Yueheng Shi, AMPUNI-centered-gap.lean, formal bias analysis for copy-based QMA amplification; context: Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.biasIter_gapRounds {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Nat) (hgap : (1 / 6 : ℝ) ≤ (q : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (gapRounds q) := by sorry
