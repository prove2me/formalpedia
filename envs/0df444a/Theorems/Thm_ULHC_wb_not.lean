-- Prove2me | Theorems.Thm_ULHC_wb_not
-- name    : ULHC.wb_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:27.831275+00:00
-- url     : https://prove2.me/theorems/af56c1a8-a3a7-4ce9-8921-5809d80a1b1a
-- title:
--   ULHC: wb not
-- statement:
--   The ULHC construction uses the wb not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L89-L90
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L89-L90

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.wb_not (s u : Bool) : wb s (!u) = - wb s u := by sorry
