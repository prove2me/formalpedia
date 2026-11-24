-- Prove2me | Theorems.Thm_ULHC_alt_no_cut
-- name    : ULHC.alt_no_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:41:09.408432+00:00
-- url     : https://prove2.me/theorems/73754879-b80b-4f10-9ddc-bf78852bffb8
-- title:
--   ULHC: alt no cut
-- statement:
--   The ULHC construction uses the alt no cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L338-L341
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L338-L341

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P) (hT : NoTypeIII V F)
include hF hB hT
omit hF

theorem ULHC.alt_no_cut {w : Pt} (hw : IsCell V w) (ha : Alt F w) (s : Side) :
    ¬ Cut P (sideEdge w s) := by sorry
