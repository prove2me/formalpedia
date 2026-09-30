-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_growth
-- name    : ShiQMACenteredGap.biasIter_growth
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-30T07:03:51.48533+00:00
-- url     : https://prove2.me/theorems/4d1acaa4-8846-46eb-995d-e49c7ea60209
-- title:
--   Majority of three amplifies a centered acceptance bias
-- statement:
--   For an initial bias $0\le d\le1/2$, let $B_0=d$ and $B_{k+1}=3B_k/2-2B_k^3$. Every round count $r$ satisfies $\min\{1/6,(4/3)^r d\}\le B_r$. Thus majority-of-three grows a small bias geometrically until it reaches a fixed constant.
-- source:
--   Yueheng Shi, AMPUNI-centered-gap.lean, formal bias analysis for copy-based QMA amplification; context: Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, Theorem 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

theorem ShiQMACenteredGap.biasIter_growth {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) (((4 : ℝ) / 3) ^ r * d) ≤ biasIter d r := by sorry
