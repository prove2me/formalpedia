-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_dyadic
-- name    : ShiQMACenteredGap.biasIter_dyadic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T00:59:56.012002+00:00
-- url     : https://prove2.me/theorems/456ae38d-4160-47fd-b4f0-1efc3c13d2d3
-- title:
--   Three majority rounds double a centered acceptance bias
-- statement:
--   For every initial centered bias $d$ between $0$ and $1/2$, and every natural number $r$, applying the majority-of-three bias update $3r$ times raises the bias to at least the smaller of $1/6$ and $2^r d$. Thus three rounds double the bias until it reaches a fixed constant.
-- source:
--   Yueheng Shi, QMA amplification Lean source, https://github.com/shiy1022/qma-amplification-lean/blob/83191f2e3fdc36033c8a99e8f9af6625d2cda2b0/proofs/AMPUNI-centered-gap.lean#L88-L95; Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false

/-- Three majority rounds suffice for each factor of two in the initial inverse bias. -/

theorem ShiQMACenteredGap.biasIter_dyadic {d : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) ((2 : ℝ) ^ r * d) ≤
      ShiQMACenteredGap.biasIter d (3 * r) := by
  sorry
