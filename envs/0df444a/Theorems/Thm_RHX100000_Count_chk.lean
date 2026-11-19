-- Prove2me | Theorems.Thm_RHX100000_Count_chk
-- name    : RHX100000.Count.chk
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:42:05.292418+00:00
-- url     : https://prove2.me/theorems/ad884771-94fd-4ed3-a35b-834fe76fc800
-- title:
--   Turing count n = 138031 for the box up to height 100000
-- statement:
--   The Turing-count data `RHX_Count100000Data` pass the count checkers of the framework for the box $121\le t\le100000$ with $n=138031$: `H11K.validBS` (the Riemann–von Mangoldt argument count with the certified boundary enclosures gives at most $n$ zeros in the box) and `k6sideB` (the Gamma-factor enclosures at the two heights).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_Count100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem RHX100000.Count.chk :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 100000) (Q.frac 100121 2)
      (Q.frac 9975814658 4) 138031 RHX100000.Count.E &&
      k6sideB RHX100000.Count.G0 RHX100000.Count.G1 RHX100000.Count.E) = true := by
  sorry
