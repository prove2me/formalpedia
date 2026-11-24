-- Prove2me | Theorems.Thm_ULHC_GridIso_adj_map
-- name    : ULHC.GridIso.adj_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:33.550637+00:00
-- url     : https://prove2.me/theorems/8e87a52f-5259-4916-abfd-86f766cdc8b1
-- title:
--   Grid Iso: adj map
-- statement:
--   The Grid Iso construction uses the adj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L35-L40
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L35-L40

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)

theorem ULHC.GridIso.adj_map {F : Finset Edge} {u v : Pt} (h : Adj F u v) : Adj (F.image I.g) (I.f u) (I.f v) := by sorry
