-- Prove2me | Theorems.Thm_ULHC_flow_cross_parity
-- name    : ULHC.flow_cross_parity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:52:49.454887+00:00
-- url     : https://prove2.me/theorems/7aa253f3-6e97-447d-8d4d-af858ffd3f27
-- title:
--   ULHC: flow cross parity
-- statement:
--   The ULHC construction uses the flow cross parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L443-L455
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L443-L455

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {G : Finset Edge}

theorem ULHC.flow_cross_parity (B : Finset Edge) {u : Pt} {l : List Pt}
    (hc : List.IsChain (Adj G) (u :: l)) :
    ∃ tf : ℤ, ∑ e ∈ B, flowL u l e = (crossL B u l : ℤ) + 2 * tf := by sorry
