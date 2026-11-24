-- Prove2me | Theorems.Thm_ULHC_alt_adj
-- name    : ULHC.alt_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:44:17.050095+00:00
-- url     : https://prove2.me/theorems/8c8334d8-dec3-4f4b-997e-5f32a75cc552
-- title:
--   ULHC: alt adj
-- statement:
--   The ULHC construction uses the alt adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L225-L228
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L225-L228

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.alt_adj {F : Finset Edge} {d : Pt} (ha : Alt F d) (tf : Side) :
    (sideEdge d tf ∈ F ↔ sideEdge d (latA tf) ∉ F) ∧ (sideEdge d tf ∈ F ↔ sideEdge d (latB tf) ∉ F) := by sorry
