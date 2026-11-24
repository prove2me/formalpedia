-- Prove2me | Theorems.Thm_ULHC_GridIso_mem_image_iff
-- name    : ULHC.GridIso.mem_image_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:20.649826+00:00
-- url     : https://prove2.me/theorems/6fc5963f-0a7f-4048-b63b-dd2e976e534e
-- title:
--   Grid Iso: mem image iff
-- statement:
--   The Grid Iso construction uses the mem image iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L75-L81
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L75-L81

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)

theorem ULHC.GridIso.mem_image_iff {F : Finset Edge} {e : Edge} : I.g e ∈ F.image I.g ↔ e ∈ F := by sorry
