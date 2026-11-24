-- Prove2me | Theorems.Thm_ULHC_notTypeIII_of_allConn
-- name    : ULHC.notTypeIII_of_allConn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:44:18.186452+00:00
-- url     : https://prove2.me/theorems/d6427170-1875-4714-bdca-ff16e90e7a4e
-- title:
--   ULHC: not Type III of all Conn
-- statement:
--   The ULHC construction uses the not Type III of all Conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L222-L223
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L222-L223

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.notTypeIII_of_allConn {V : Finset Pt} {F : Finset Edge} {d : Pt} (h : AllConn F d) :
    NotTypeIII V F d := by sorry
