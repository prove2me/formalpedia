-- Prove2me | Theorems.Thm_ULHC_flip_split
-- name    : ULHC.flip_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:28.779801+00:00
-- url     : https://prove2.me/theorems/b661c197-fa29-4dbe-a6ce-0f96fce97208
-- title:
--   ULHC: flip split
-- statement:
--   The ULHC construction uses the flip split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L157-L301
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L157-L301

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

theorem ULHC.flip_split (hy : Conn F (x, y) (x, y + 1)) (hle : ∀ z, deg F z ≤ 2) :
    ncomp V (flip F (x, y)) = ncomp V F + 1 := by sorry
