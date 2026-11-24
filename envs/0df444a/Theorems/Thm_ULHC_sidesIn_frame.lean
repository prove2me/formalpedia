-- Prove2me | Theorems.Thm_ULHC_sidesIn_frame
-- name    : ULHC.sidesIn_frame
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:03.081079+00:00
-- url     : https://prove2.me/theorems/65589c82-7c12-46d4-9085-bed4d0393131
-- title:
--   ULHC: sides In frame
-- statement:
--   The ULHC construction uses the sides In frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L157-L159
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L157-L159

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sidesIn_frame (B : Finset Edge) (d : Pt) (s : Side) :
    sidesIn B d = ind B (back d s) + ind B (front d s) + ind B (lat1 d s) + ind B (lat2 d s) := by sorry
