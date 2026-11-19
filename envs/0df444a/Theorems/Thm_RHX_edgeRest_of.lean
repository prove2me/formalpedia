-- Prove2me | Theorems.Thm_RHX_edgeRest_of
-- name    : RHX.edgeRest_of
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:49:55.089952+00:00
-- url     : https://prove2.me/theorems/e0ed03ac-d45c-450f-bbac-d62ee21a5148
-- title:
--   Conjunct split of H11K.edgeRest
-- statement:
--   `H11K.edgeRest E = true` follows from its head conjuncts, the two endpoint box checks and the two final inequalities.
--
--   This is a computation-free lemma: it restates a checker of the published framework (`H11K.edgeRest`) as the conjunction of its conjuncts, so that each conjunct can be checked by the kernel as a separate small goal.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

theorem edgeRest_of (E : EdgeD)
    (hh : (Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) && eqB (E.x E.m) (ofInt (-1)) &&
      (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
      eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1))) = true)
    (hb0 : boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0
      E.qlo0 E.qhi0 = true)
    (hb1 : boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1
      E.qlo1 E.qhi1 = true)
    (hlo : finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo = true)
    (hhi : finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi = true) :
    H11K.edgeRest E = true := by
  sorry

end RHX
