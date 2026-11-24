-- Prove2me | Theorems.Thm_ULHC_TF_sum_deg_black
-- name    : ULHC.TF.sum_deg_black
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:46:40.506344+00:00
-- url     : https://prove2.me/theorems/1ffb942c-4c9d-4bb0-b379-5de4cd9e34e2
-- title:
--   TF: sum deg black
-- statement:
--   The TF construction uses the sum deg black property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L571-L577
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L571-L577

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.sum_deg_black {V : Finset Pt} {F : Finset Edge} (hF : Inside V F) :
    ∑ z ∈ V.filter Black, deg F z = F.card := by sorry
