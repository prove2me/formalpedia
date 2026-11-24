-- Prove2me | Theorems.Thm_ULHC_sidesIn_insert
-- name    : ULHC.sidesIn_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:49:23.496889+00:00
-- url     : https://prove2.me/theorems/30425ff4-be40-42ba-934e-5e10cf52656f
-- title:
--   ULHC: sides In insert
-- statement:
--   The ULHC construction uses the sides In insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L34-L52
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L34-L52

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sidesIn_insert (e : Edge) (B : Finset Edge) (x : Pt) (he : e ∉ B) :
    sidesIn (insert e B) x = sidesIn B x + if e ∈ cellE x then 1 else 0 := by sorry
