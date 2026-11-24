-- Prove2me | Theorems.Thm_ULHC_Adj_symm
-- name    : ULHC.Adj.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:32.506798+00:00
-- url     : https://prove2.me/theorems/9229fc0f-33d2-4fbe-b7e2-b1673148dd92
-- title:
--   Adj: symm
-- statement:
--   The Adj construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L26-L27
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Conn.lean#L26-L27

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
set_option autoImplicit true
open ULHC

theorem ULHC.Adj.symm {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Adj F b a := by sorry
