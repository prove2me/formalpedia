-- Prove2me | Theorems.Thm_ULHC_Ends_conn_iff
-- name    : ULHC.Ends.conn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:58.186399+00:00
-- url     : https://prove2.me/theorems/da45a59b-c200-4067-b689-7df32780ca55
-- title:
--   Ends: conn iff
-- statement:
--   The Ends construction uses the conn iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L33-L35
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L33-L35

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}

theorem ULHC.Ends.conn_iff (h : Ends e u v) (F : Finset Edge) : Conn F e.p e.q ↔ Conn F u v := by sorry
