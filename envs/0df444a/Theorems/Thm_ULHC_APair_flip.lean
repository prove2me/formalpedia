-- Prove2me | Theorems.Thm_ULHC_APair_flip
-- name    : ULHC.APair.flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:27.86537+00:00
-- url     : https://prove2.me/theorems/c8ea7db3-b645-4e7b-9650-0a40c96898fc
-- title:
--   APair: flip
-- statement:
--   The APair construction uses the flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L473-L638
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L473-L638

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (P : APair)
  (hV : Inside V F) (hVa : P.a ∈ V) (hVb : P.b ∈ V) (hVm1 : P.m1 ∈ V) (hVm2 : P.m2 ∈ V)
  (hVt1 : P.t1 ∈ V) (hVt2 : P.t2 ∈ V)
  (heam : P.eam ∈ F) (hebm : P.ebm ∈ F) (hem : P.em ∈ F) (het : P.et ∈ F)
  (hd1 : deg F P.m1 = 2) (hd2 : deg F P.m2 = 2)
include hV hVa hVb hVm1 hVm2 hVt1 hVt2 heam hebm hem het hd1 hd2
omit hV hVa hVt2

theorem ULHC.APair.flip :
    ncomp V (P.res F) = ncomp V F ∧
      ∀ x y, x ≠ P.m1 → x ≠ P.m2 → y ≠ P.m1 → y ≠ P.m2 →
        (Conn (P.res F) x y ↔ Conn F x y) := by sorry
