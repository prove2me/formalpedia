-- Prove2me | Theorems.Thm_RHX_pieceOK_of
-- name    : RHX.pieceOK_of
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:49:53.521706+00:00
-- url     : https://prove2.me/theorems/dd3a5936-953a-4ed7-a4f6-361aca81c277
-- title:
--   Conjunct split of Arb4.pieceOK
-- statement:
--   `Arb4.pieceOK tn tq N L P = true` follows from its nine conjuncts, with the evaluator states written out.
--
--   This is a computation-free lemma: it restates a checker of the published framework (`Arb4.pieceOK`) as the conjunction of its conjuncts, so that each conjunct can be checked by the kernel as a separate small goal.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
set_option maxRecDepth 100000
open Arb4

namespace RHX

theorem pieceOK_of (tn tq N : ℕ) (L : Q) (P : PieceD)
    (h0 : (Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 P.rd && Nat.ble 1 P.FD) = true)
    (hc : (let c := ArbEcon.OrderK.cfg64 tn tq
      let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c P.oc 1 s1
      H1000Oct.checkOct c P.oc 6 N 5 s1.acc sN.acc P.rn P.rd P.FN P.FD P.kk) = true)
    (hg : (let c := ArbEcon.OrderK.cfg64 tn tq
      let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c P.oc 1 s1
      geomOK tn tq L sN.lhi P) = true)
    (hG : gOK N P = true) (hr : remOK tn tq N P = true) (hb : budgetOK N L P = true) :
    pieceOK tn tq N L P = true := by
  sorry

end RHX
