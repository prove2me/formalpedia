-- Prove2me | Theorems.Thm_ULHC_flip_eq
-- name    : ULHC.flip_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:25.501265+00:00
-- url     : https://prove2.me/theorems/b007b675-e5b3-4b7c-8f7e-4ca66b7b4d38
-- title:
--   ULHC: flip eq
-- statement:
--   The ULHC construction uses the flip eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L52-L75
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Flip.lean#L52-L75

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.flip_eq {F : Finset Edge} {c : Pt} (hb : bot c ∈ F) (ht : top c ∈ F) (hl : lft c ∉ F)
    (hr : rgt c ∉ F) :
    flip F c = insert (rgt c) (insert (lft c) ((F.erase (bot c)).erase (top c))) := by sorry
