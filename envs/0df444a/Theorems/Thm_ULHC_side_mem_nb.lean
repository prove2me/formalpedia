-- Prove2me | Theorems.Thm_ULHC_side_mem_nb
-- name    : ULHC.side_mem_nb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:26:48.193637+00:00
-- url     : https://prove2.me/theorems/38476acf-a7fb-48ea-836e-7b81af9174ac
-- title:
--   ULHC: side mem nb
-- statement:
--   The ULHC construction uses the side mem nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L27-L29
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearGeo.lean#L27-L29

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.side_mem_nb (c : Pt) (tf : Side) : sideEdge c tf ∈ cellE (nb c tf) := by sorry
