-- Prove2me | Theorems.Thm_ULHC_flowL_mem
-- name    : ULHC.flowL_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:52:50.500069+00:00
-- url     : https://prove2.me/theorems/c59d06fa-cfff-4162-baaa-f4ea05e81108
-- title:
--   ULHC: flow L mem
-- statement:
--   The ULHC construction uses the flow L mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L395-L406
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L395-L406

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {G : Finset Edge}

theorem ULHC.flowL_mem {u : Pt} {l : List Pt} (hc : List.IsChain (Adj G) (u :: l)) {e : Edge}
    (h : flowL u l e ≠ 0) : e ∈ G := by sorry
