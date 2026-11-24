-- Prove2me | Theorems.Thm_ULHC_GridIso_conn_iff
-- name    : ULHC.GridIso.conn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:49:36.707004+00:00
-- url     : https://prove2.me/theorems/8b743f35-bc38-45e4-a58a-1a62ced913cd
-- title:
--   Grid Iso: conn iff
-- statement:
--   The Grid Iso construction uses the conn iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L65-L73
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Iso.lean#L65-L73

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
import Theorems.Thm_ULHC_Ends_conn_iff

set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)

theorem ULHC.GridIso.conn_iff {F : Finset Edge} {u v : Pt} :
    Conn (F.image I.g) (I.f u) (I.f v) ↔ Conn F u v := by sorry
