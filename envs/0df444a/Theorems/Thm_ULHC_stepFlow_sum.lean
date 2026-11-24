-- Prove2me | Theorems.Thm_ULHC_stepFlow_sum
-- name    : ULHC.stepFlow_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:52:52.343485+00:00
-- url     : https://prove2.me/theorems/bbd367fa-1703-45e3-a967-692217a26da7
-- title:
--   ULHC: step Flow sum
-- statement:
--   The ULHC construction uses the step Flow sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L408-L441
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L408-L441

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {G : Finset Edge}

theorem ULHC.stepFlow_sum {u v : Pt} (h : Adj G u v) (B : Finset Edge) :
    ∃ tf : ℤ, ∑ e ∈ B, stepFlow u v e = (if ∃ e ∈ B, Ends e u v then 1 else 0) + 2 * tf := by sorry
