-- Prove2me | Theorems.Thm_ULHC_sum_hi_lo
-- name    : ULHC.sum_hi_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:52:56.684639+00:00
-- url     : https://prove2.me/theorems/cd7883d6-1451-4bd7-a39b-75f3be9b7e56
-- title:
--   ULHC: sum hi lo
-- statement:
--   The ULHC construction uses the sum hi lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L349-L387
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L349-L387

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sum_hi_lo (B : Finset Edge) (W : Pt → ℤ) (T : Finset Pt)
    (hT : ∀ e ∈ B, e.hi ∈ T ∧ e.lo ∈ T) :
    ∑ e ∈ B, (W e.hi + W e.lo) = ∑ c ∈ T, W c * (sidesIn B c : ℤ) := by sorry
