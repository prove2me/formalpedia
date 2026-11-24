-- Prove2me | Theorems.Thm_ULHC_GridIso_conn_map
-- name    : ULHC.GridIso.conn_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:14.383932+00:00
-- url     : https://prove2.me/theorems/bfa6711f-40cc-4396-bdf0-80b7ca94f44f
-- title:
--   Grid Iso: conn map
-- statement:
--   The Grid Iso construction uses the conn map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L42-L44
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L42-L44

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
import Theorems.Thm_ULHC_conn_map

set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)

theorem ULHC.GridIso.conn_map {F : Finset Edge} {u v : Pt} (h : Conn F u v) :
    Conn (F.image I.g) (I.f u) (I.f v) := by sorry
