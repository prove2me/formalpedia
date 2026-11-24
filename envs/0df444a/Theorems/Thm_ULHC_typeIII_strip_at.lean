-- Prove2me | Theorems.Thm_ULHC_typeIII_strip_at
-- name    : ULHC.typeIII_strip_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:45:47.855407+00:00
-- url     : https://prove2.me/theorems/4454b532-84c6-42e9-be0f-57e203637fe2
-- title:
--   ULHC: type III strip at
-- statement:
--   The ULHC construction uses the type III strip at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L49-L59
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L49-L59

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.typeIII_strip_at {V : Finset Pt} {F : Finset Edge} {d : Pt} (hd : IsCell V d)
    (h : ¬ NotTypeIII V F d) : ∃ σ : StripSpec, σ.c = d ∧ ValidStrip V F σ ∧ σ.n % 2 = 1 := by sorry
