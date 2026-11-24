-- Prove2me | Theorems.Thm_ULHC_alt_no_cut_l
-- name    : ULHC.alt_no_cut_l
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:18:27.959513+00:00
-- url     : https://prove2.me/theorems/392dfb84-a744-4b52-8fbf-db341759c01a
-- title:
--   ULHC: alt no cut l
-- statement:
--   The ULHC construction uses the alt no cut l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L254-L257
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L254-L257

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P)
include hF hB
omit hF

theorem ULHC.alt_no_cut_l {w : Pt} (hTw : NotTypeIII V F w) (ha : Alt F w) (s : Side) :
    ¬ Cut P (sideEdge w s) := by sorry
