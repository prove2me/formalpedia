-- Prove2me | Theorems.Thm_ULHC_ACell_split
-- name    : ULHC.ACell.split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:28.461088+00:00
-- url     : https://prove2.me/theorems/d5a44182-8427-4e26-b1a4-2934b0cab9cb
-- title:
--   ACell: split
-- statement:
--   The ACell construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L210-L386
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L210-L386

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
omit hl2

theorem ULHC.ACell.split (hy : Conn F C.a C.d) (hle : ∀ z, deg F z ≤ 2)
    (hplanar : ∀ G : Finset Edge, C.e1 ∉ G → C.l1 ∉ G → Conn G C.b C.d → Conn G C.k C.a →
      ¬ Conn G C.a C.b → False) :
    ncomp V (C.res F) = ncomp V F + 1 ∧ (∀ u v, Conn (C.res F) u v → Conn F u v) ∧
      ∀ u v, Conn F u v ↔ Conn (C.res F) u v ∨ (Conn (C.res F) u C.a ∧ Conn (C.res F) C.b v) ∨
        (Conn (C.res F) u C.b ∧ Conn (C.res F) C.a v) := by sorry
