-- Prove2me | Theorems.Thm_ULHC_cell_of_side
-- name    : ULHC.cell_of_side
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:30:09.221672+00:00
-- url     : https://prove2.me/theorems/1beae00d-e628-41da-99a1-80167dbcec3b
-- title:
--   ULHC: cell of side
-- statement:
--   The ULHC construction uses the cell of side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L26-L31
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L26-L31

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.cell_of_side {d : Pt} {tf : Side} (h : sideEdge c tf ∈ cellE d) : d = c ∨ d = nb c tf := by sorry
