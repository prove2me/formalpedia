-- Prove2me | Theorems.Thm_ULHC_front1_not_corner
-- name    : ULHC.front1_not_corner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:03:58.162691+00:00
-- url     : https://prove2.me/theorems/3a3b99bf-e124-4841-9ba8-367e6393185d
-- title:
--   ULHC: front1 not corner
-- statement:
--   The ULHC construction uses the front1 not corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L720-L723
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L720-L723

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.front1_not_corner (d : Pt) (s : Side) :
    front1 (nb d s) s ∉ ({back1 d s, back2 d s, front1 d s, front2 d s} : Finset Pt) := by sorry
