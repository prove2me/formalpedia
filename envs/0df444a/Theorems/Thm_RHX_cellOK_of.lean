-- Prove2me | Theorems.Thm_RHX_cellOK_of
-- name    : RHX.cellOK_of
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:49:52.505438+00:00
-- url     : https://prove2.me/theorems/760ef9b9-d4c1-4ebf-b9df-a24b54f63b0f
-- title:
--   Conjunct split of Arb4.cellOK
-- statement:
--   `Arb4.cellOK S j = true` follows from its fourteen conjuncts, with the evaluator states written out.
--
--   This is a computation-free lemma: it restates a checker of the published framework (`Arb4.cellOK`) as the conjunction of its conjuncts, so that each conjunct can be checked by the kernel as a separate small goal.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

theorem cellOK_of (S : SlabD) (j : ℕ)
    (h0 : (Nat.ble 2 S.N && Nat.ble 1 (S.cell j).q && Nat.ble 1 (S.cell j).rd &&
      Nat.ble (S.cell j).b (S.cell j).a) = true)
    (hc : (let c := ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq
      let s1 := ArbEcon.Off.runO c (S.cell j).oc (S.N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c (S.cell j).oc 1 s1
      ArbEcon.Off.checkCell c (S.cell j).oc 6 S.N 5 s1.acc sN.acc (S.cell j).rn (S.cell j).rd S.FN S.FD) = true)
    (hR : le (frac ((S.cell j).rn : ℤ) (S.cell j).rd) S.R = true)
    (hl : (let c := ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq
      let s1 := ArbEcon.Off.runO c (S.cell j).oc (S.N - 2) (ArbEcon.Off.StO.init c 5)
      let sN := ArbEcon.Off.runO c (S.cell j).oc 1 s1
      le (ofNat sN.lhi) (mul S.L (ofNat (2 ^ 64)))) = true)
    (r1 : le S.lo (tQ (S.cell j).tn S.tq) = true)
    (r2 : le (add (npow (add (S.cell j).σQ (ofNat 11)) 2) (npow (tQ (S.cell j).tn S.tq) 2)) (npow S.U 2) = true)
    (r3 : le (qabs (sub (S.xs j) (S.cell j).σQ)) (S.cell j).w = true)
    (r4 : le (qabs (sub (S.xs (j + 1)) (S.cell j).σQ)) (S.cell j).w = true)
    (r5 : le (qabs (sub S.lo (tQ (S.cell j).tn S.tq))) (S.cell j).hh = true)
    (r6 : le (qabs (sub S.hi (tQ (S.cell j).tn S.tq))) (S.cell j).hh = true)
    (r7 : le (add (npow (S.cell j).w 2) (npow (S.cell j).hh 2)) (npow (frac ((S.cell j).rn : ℤ) (S.cell j).rd) 2) = true) :
    cellOK S j = true := by
  sorry

end RHX
