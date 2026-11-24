-- Prove2me | Theorems.Thm_ULHC_four_sides_class
-- name    : ULHC.four_sides_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:35:31.79207+00:00
-- url     : https://prove2.me/theorems/800d1b9a-2276-4e78-83e1-8041789a1e89
-- title:
--   ULHC: four sides class
-- statement:
--   The ULHC construction uses the four sides class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L255-L289
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L255-L289

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.four_sides_class {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {g : Pt} (hg : IsCell V g)
    (tf : Side) (h1 : back g tf ∈ F) (h2 : front g tf ∈ F) (h3 : lat1 g tf ∈ F) (h4 : lat2 g tf ∈ F)
    {z : Pt} (hz : Conn F (back1 g tf) z) :
    z ∈ ({back1 g tf, back2 g tf, front1 g tf, front2 g tf} : Finset Pt) := by sorry
