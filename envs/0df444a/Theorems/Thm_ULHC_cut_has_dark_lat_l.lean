-- Prove2me | Theorems.Thm_ULHC_cut_has_dark_lat_l
-- name    : ULHC.cut_has_dark_lat_l
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:48:10.420901+00:00
-- url     : https://prove2.me/theorems/a6a82e16-07d6-462c-becc-32d4f42dde1c
-- title:
--   ULHC: cut has dark lat l
-- statement:
--   The ULHC construction uses the cut has dark lat l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L261-L324
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L261-L324

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P)
include hF hB

theorem ULHC.cut_has_dark_lat_l {w : Pt} (hw : IsCell V w) (s : Side) (hcut : Cut P (sideEdge w s))
    (hTr : IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by sorry
