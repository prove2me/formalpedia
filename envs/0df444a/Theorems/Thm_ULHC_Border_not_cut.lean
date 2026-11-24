-- Prove2me | Theorems.Thm_ULHC_Border_not_cut
-- name    : ULHC.Border.not_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:26:10.142987+00:00
-- url     : https://prove2.me/theorems/2ba0de04-969c-45eb-b7aa-1c7e9c2e0b7a
-- title:
--   Border: not cut
-- statement:
--   The Border construction uses the not cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L104-L109
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L104-L109

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.Border.not_cut {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {e : Edge} (he : e ∈ F) : ¬ Cut P e := by sorry
