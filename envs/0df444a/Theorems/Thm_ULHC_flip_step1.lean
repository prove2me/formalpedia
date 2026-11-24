-- Prove2me | Theorems.Thm_ULHC_flip_step1
-- name    : ULHC.flip_step1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:36.7348+00:00
-- url     : https://prove2.me/theorems/c1a1656b-709c-4a6d-b86e-7ca658f3dce6
-- title:
--   ULHC: flip step1
-- statement:
--   The ULHC construction uses the flip step1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L88-L100
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L88-L100

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {x y : ℤ}
  (hV : Inside V F) (hc : IsCell V (x, y))
  (hb : bot (x, y) ∈ F) (ht : top (x, y) ∈ F) (hl : lft (x, y) ∉ F) (hr : rgt (x, y) ∉ F)
  (h2 : ∀ z, (Conn F (x, y) z ∨ Conn F (x, y + 1) z) → deg F z = 2)
include hV hc hb ht hl hr h2
omit hc ht hl hr

theorem ULHC.flip_step1 :
    Conn (F.erase (bot (x, y))) (x, y) (x + 1, y) ∧
      ncomp V (F.erase (bot (x, y))) = ncomp V F := by sorry
