-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_standard
-- name    : ShiQMACenteredGap.biasIter_standard
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T01:12:56.625987+00:00
-- url     : https://prove2.me/theorems/4c6c51b5-dde8-4b66-a8e2-d0a4f4fd6e2a
-- title:
--   Centered majority bias equals half minus majority error
-- statement:
--   Starting at centered bias $1/6$, after any $r$ majority-of-three rounds the bias is exactly $1/2$ minus the standard majority-error recurrence after $r$ rounds. This identifies the centered and error viewpoints used in the QMA amplification schedule.
-- source:
--   Yueheng Shi, QMA amplification Lean source, https://github.com/shiy1022/qma-amplification-lean/blob/83191f2e3fdc36033c8a99e8f9af6625d2cda2b0/proofs/AMPUNI-general-gap-schedule.lean#L23-L29; Marriott and Watrous, Quantum Arthur–Merlin Games (2005), Section 3, https://cs.uwaterloo.ca/~watrous/Papers/QuantumArthurMerlinGames.pdf

import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false

/-- Centered majority bias is the complement of the standard error recurrence. -/

theorem ShiQMACenteredGap.biasIter_standard (r : Nat) :
    ShiQMACenteredGap.biasIter (1 / 6) r =
      1 / 2 - ShiQMAErrorIteration.error r := by
  sorry
