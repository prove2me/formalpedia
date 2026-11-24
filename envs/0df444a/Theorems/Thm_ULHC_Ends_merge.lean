-- Prove2me | Theorems.Thm_ULHC_Ends_merge
-- name    : ULHC.Ends.merge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:21.569952+00:00
-- url     : https://prove2.me/theorems/b8de1332-7272-4299-96ce-ba662a3b22d1
-- title:
--   Ends: merge
-- statement:
--   The Ends construction uses the merge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L56-L61
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L56-L61

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}

theorem ULHC.Ends.merge {V : Finset Pt} {F : Finset Edge} (h : Ends e u v) (hu : u ∈ V) (hv : v ∈ V)
    (hn : ¬ Conn F u v) : ncomp V (insert e F) + 1 = ncomp V F := by sorry
