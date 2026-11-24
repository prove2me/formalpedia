-- Prove2me | Theorems.Thm_ULHC_bot_ne_lft
-- name    : ULHC.bot_ne_lft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:52:01.539803+00:00
-- url     : https://prove2.me/theorems/ec516da0-c2f6-49bf-b9db-77b7f28c78fe
-- title:
--   ULHC: bot ne lft
-- statement:
--   The ULHC construction uses the bot ne lft property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L346-L346
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L346-L346

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.bot_ne_lft (c : Pt) : bot c ≠ lft c := by sorry
