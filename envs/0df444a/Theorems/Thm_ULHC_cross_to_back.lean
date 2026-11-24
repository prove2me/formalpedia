-- Prove2me | Theorems.Thm_ULHC_cross_to_back
-- name    : ULHC.cross_to_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:27:23.711424+00:00
-- url     : https://prove2.me/theorems/45fc107b-f164-4973-8367-eb2016606cd2
-- title:
--   ULHC: cross to back
-- statement:
--   The ULHC construction uses the cross to back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L138-L145
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean#L138-L145

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.cross_to_back {A : Finset Edge} {d : Pt} {s tf : Side} (ht : tf = latA s ∨ tf = latB s)
    (h1 : lat1 d s ∈ A) (h2 : lat2 d s ∈ A) (hn : ¬ Conn A (back1 d tf) (front1 d tf)) :
    ¬ Conn A (back1 d s) (back2 d s) := by sorry
