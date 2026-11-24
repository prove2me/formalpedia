-- Prove2me | Theorems.Thm_ULHC_conn_insert_of_conn
-- name    : ULHC.conn_insert_of_conn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:06.308144+00:00
-- url     : https://prove2.me/theorems/aed4c0c0-0eaa-48d9-9a13-fb70f5042e69
-- title:
--   ULHC: conn insert of conn
-- statement:
--   The ULHC construction uses the conn insert of conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L77-L85
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L77-L85

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.conn_insert_of_conn {F : Finset Edge} {e : Edge} (h : Conn F e.p e.q) (x y : Pt) :
    Conn (insert e F) x y ↔ Conn F x y := by sorry
