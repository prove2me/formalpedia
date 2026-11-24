-- Prove2me | Theorems.Thm_ULHC_NoTypeIII_at
-- name    : ULHC.NoTypeIII.at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:05.359947+00:00
-- url     : https://prove2.me/theorems/b4d40254-8bdf-47de-8644-39e40c12646f
-- title:
--   No Type III: at
-- statement:
--   The No Type III construction uses the at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L206-L207
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L206-L207

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.NoTypeIII.at {V : Finset Pt} {F : Finset Edge} (hT : NoTypeIII V F) {c : Pt}
    (hc : IsCell V c) : NotTypeIII V F c := by sorry
