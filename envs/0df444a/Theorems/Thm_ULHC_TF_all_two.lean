-- Prove2me | Theorems.Thm_ULHC_TF_all_two
-- name    : ULHC.TF.all_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:48:46.72562+00:00
-- url     : https://prove2.me/theorems/e69f028a-347b-45ec-86b4-28ebeef11e41
-- title:
--   TF: all two
-- statement:
--   The TF construction uses the all two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L560-L566
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L560-L566

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.all_two {S : Finset Pt} {f : Pt → ℕ} (hle : ∀ z ∈ S, f z ≤ 2)
    (hsum : 2 * S.card ≤ ∑ z ∈ S, f z) : ∀ z ∈ S, f z = 2 := by sorry
