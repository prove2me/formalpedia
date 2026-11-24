-- Prove2me | Theorems.Thm_ULHC_ACell_merge
-- name    : ULHC.ACell.merge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:49:12.274859+00:00
-- url     : https://prove2.me/theorems/3af2214e-b14b-4b06-8a35-c5623332a20e
-- title:
--   ACell: merge
-- statement:
--   The ACell construction uses the merge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L136-L205
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L136-L205

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (C : ACell)
  (hV : Inside V F) (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
  (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F) (hl1 : C.l1 ∉ F) (hl2 : C.l2 ∉ F)
  (hdeg2 : ∀ z, (Conn F C.a z ∨ Conn F C.d z) → deg F z = 2)
include hV hVa hVb hVd hVk he1 he2 hl1 hl2 hdeg2
omit hVb hVk hl1 hl2

theorem ULHC.ACell.merge (hn : ¬ Conn F C.a C.d) :
    ncomp V (C.res F) + 1 = ncomp V F ∧
      ∀ x y, Conn (C.res F) x y ↔
        Conn F x y ∨ (Conn F x C.a ∧ Conn F C.d y) ∨ (Conn F x C.d ∧ Conn F C.a y) := by sorry
