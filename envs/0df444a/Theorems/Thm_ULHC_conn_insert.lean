-- Prove2me | Theorems.Thm_ULHC_conn_insert
-- name    : ULHC.conn_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:51.43581+00:00
-- url     : https://prove2.me/theorems/20d7bce7-c40a-47c9-b424-899dc9ce3d41
-- title:
--   ULHC: conn insert
-- statement:
--   The ULHC construction uses the conn insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L44-L73
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L44-L73

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.conn_insert {F : Finset Edge} {e : Edge} {x y : Pt} :
    Conn (insert e F) x y ↔
      Conn F x y ∨ (Conn F x e.p ∧ Conn F e.q y) ∨ (Conn F x e.q ∧ Conn F e.p y) := by sorry
