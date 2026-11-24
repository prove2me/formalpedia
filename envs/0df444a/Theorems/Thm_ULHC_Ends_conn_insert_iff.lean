-- Prove2me | Theorems.Thm_ULHC_Ends_conn_insert_iff
-- name    : ULHC.Ends.conn_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:51.303679+00:00
-- url     : https://prove2.me/theorems/eae1171f-07ab-42ea-acd5-b2c4a5628d12
-- title:
--   Ends: conn insert iff
-- statement:
--   The Ends construction uses the conn insert iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L49-L54
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L49-L54

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}

theorem ULHC.Ends.conn_insert_iff {F : Finset Edge} (h : Ends e u v) (x y : Pt) :
    Conn (insert e F) x y ↔
      Conn F x y ∨ (Conn F x u ∧ Conn F v y) ∨ (Conn F x v ∧ Conn F u y) := by sorry
