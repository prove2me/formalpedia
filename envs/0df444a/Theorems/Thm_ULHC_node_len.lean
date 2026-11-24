-- Prove2me | Theorems.Thm_ULHC_node_len
-- name    : ULHC.node_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:09:17.960624+00:00
-- url     : https://prove2.me/theorems/980b6e9b-b294-4860-91d6-d8a0a1320852
-- title:
--   ULHC: node len
-- statement:
--   The ULHC construction uses the node len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostStrips.lean#L128-L131
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostStrips.lean#L128-L131

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.node_len (x : Node) (hx : x ∈ candN V G) : 1 ≤ x.σ.n ∧ x.σ.n ≤ V.card ∧
    ∀ j < x.σ.n, IsCell V (cellJ x.σ.c x.σ.s j) := by sorry
