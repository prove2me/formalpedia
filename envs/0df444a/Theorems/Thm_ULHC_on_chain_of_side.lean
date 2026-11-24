-- Prove2me | Theorems.Thm_ULHC_on_chain_of_side
-- name    : ULHC.on_chain_of_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:10.728483+00:00
-- url     : https://prove2.me/theorems/47a96e73-c51b-4d9d-9c1a-5bad446f5d54
-- title:
--   ULHC: on chain of side
-- statement:
--   The ULHC construction uses the on chain of side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L826-L831
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L826-L831

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.on_chain_of_side {c0 w : Pt} {e : Edge} (hw : IsCell V w) (he : e ∈ cellE w)
    (hB : e ∈ EB V F c0) : w ∈ chainCells V F c0 := by sorry
