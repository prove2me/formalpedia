-- Prove2me | Theorems.Thm_ULHC_stop_of_not_out
-- name    : ULHC.stop_of_not_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:48:22.696261+00:00
-- url     : https://prove2.me/theorems/e210a132-e6dd-4f74-8569-56f4dfd263da
-- title:
--   ULHC: stop of not out
-- statement:
--   The ULHC construction uses the stop of not out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L113-L120
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase.lean#L113-L120

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
include hF hB hT

theorem ULHC.stop_of_not_out {w : Pt} (hw : IsCell V w) (he : Entered F P o w)
    (hno : ¬ Out F P o w) : Stop F P o w := by sorry
