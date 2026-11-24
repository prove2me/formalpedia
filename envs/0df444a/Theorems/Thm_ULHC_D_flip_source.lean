-- Prove2me | Theorems.Thm_ULHC_D_flip_source
-- name    : ULHC.D_flip_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:27.467796+00:00
-- url     : https://prove2.me/theorems/da2abeb5-3f48-4b92-ba71-47f4dde86657
-- title:
--   ULHC: D flip source
-- statement:
--   The ULHC construction uses the D flip source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L292-L302
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L292-L302

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.D_flip_source {F H : Finset Edge} {c : Pt} (h : Source F c) (x : Pt) :
    D (flip F c) H x = D F H x + (if x = c then 2 else 0) := by sorry
