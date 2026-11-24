-- Prove2me | Theorems.Thm_ULHC_seq_count
-- name    : ULHC.seq_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:37:52.102627+00:00
-- url     : https://prove2.me/theorems/e8518d31-73ce-42f9-b274-a857599e60a9
-- title:
--   ULHC: seq count
-- statement:
--   The ULHC construction uses the seq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L119-L139
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L119-L139

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.seq_count {V : Finset Pt} :
    ∀ (L : List StripSpec) (F : Finset Edge), Deg2 V F → ValidSeq V F L →
      ncomp V (applySeq F L) + 1 = ncomp V F := by sorry
