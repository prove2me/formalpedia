-- Prove2me | Theorems.Thm_ULHC_wD_balanced_at
-- name    : ULHC.wD_balanced_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:10.212036+00:00
-- url     : https://prove2.me/theorems/02356c92-5445-49c8-9f7c-1d0314f8dbfc
-- title:
--   ULHC: w D balanced at
-- statement:
--   The ULHC construction uses the w D balanced at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L41-L60
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L41-L60

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.wD_balanced_at (F H : Finset Edge) (p : Pt) (hdeg : deg F p = deg H p) :
    wD F H (eD p) + wD F H (eR p) = wD F H (eL p) + wD F H (eU p) := by sorry
