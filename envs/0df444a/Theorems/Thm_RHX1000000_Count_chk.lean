-- Prove2me | Theorems.Thm_RHX1000000_Count_chk
-- name    : RHX1000000.Count.chk
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:50:50.762236+00:00
-- url     : https://prove2.me/theorems/0728c1a5-10c5-4fb0-ac44-31884ddcf80a
-- title:
--   Turing count n = 1747108 for the box up to height 1000000
-- statement:
--   The count data `RHX_Count1000000Data` pass the count checkers of the framework for the box $121\le t\le10^6$ with $n=1747108$: `H11K.validBS` (the argument-principle count with the certified boundary enclosures gives at most $n$ zeros in the box) and `k6sideB` (the Gamma-factor enclosures at the two heights).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_Count1000000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem RHX1000000.Count.chk :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 1000000) (Q.frac 1000121 2)
      (Q.frac 999758014658 4) 1747108 RHX1000000.Count.E &&
      k6sideB RHX1000000.Count.G0 RHX1000000.Count.G1 RHX1000000.Count.E) = true := by
  sorry
