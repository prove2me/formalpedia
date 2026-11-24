-- Prove2me | Theorems.Thm_ULHC_wD_supp
-- name    : ULHC.wD_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:40.365608+00:00
-- url     : https://prove2.me/theorems/b5e86b3e-e837-4459-8409-f547e1d70ab9
-- title:
--   ULHC: w D supp
-- statement:
--   The ULHC construction uses the w D supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L33-L37
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L33-L37

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.wD_supp (F H : Finset Edge) : Supp (symmDiff F H) (wD F H) := by sorry
