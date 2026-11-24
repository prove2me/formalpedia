-- Prove2me | Theorems.Thm_ULHC_cut_has_dark_lat
-- name    : ULHC.cut_has_dark_lat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:43.341147+00:00
-- url     : https://prove2.me/theorems/e13df028-4d7b-4795-b02b-541f135eaaf4
-- title:
--   ULHC: cut has dark lat
-- statement:
--   The ULHC construction uses the cut has dark lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L345-L407
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L345-L407

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P) (hT : NoTypeIII V F)
include hF hB hT

theorem ULHC.cut_has_dark_lat {w : Pt} (hw : IsCell V w) (s : Side) (hcut : Cut P (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by sorry
