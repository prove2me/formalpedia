-- Prove2me | Theorems.Thm_ULHC_symmDiff_six
-- name    : ULHC.symmDiff_six
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:47:21.725002+00:00
-- url     : https://prove2.me/theorems/ddfd376f-dcfb-43d7-b046-f5096239fd92
-- title:
--   ULHC: symm Diff six
-- statement:
--   The ULHC construction uses the symm Diff six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L192-L221
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L192-L221

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.symmDiff_six {F : Finset Edge} {a1 a2 a3 b1 b2 b3 : Edge}
    (ha1 : a1 ∈ F) (ha2 : a2 ∈ F) (ha3 : a3 ∈ F) (hb1 : b1 ∉ F) (hb2 : b2 ∉ F) (hb3 : b3 ∉ F) :
    symmDiff F {b1, a1, a2, a3, b2, b3} =
      (insert b3 (insert b2 (((insert b1 F).erase a1).erase a2))).erase a3 := by sorry
