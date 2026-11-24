-- Prove2me | Theorems.Thm_ULHC_TF_sum_deg_white
-- name    : ULHC.TF.sum_deg_white
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:46:37.498924+00:00
-- url     : https://prove2.me/theorems/b5f6b07b-c016-43e6-ad4d-842323c6f65c
-- title:
--   TF: sum deg white
-- statement:
--   The TF construction uses the sum deg white property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L579-L585
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L579-L585

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.sum_deg_white {V : Finset Pt} {F : Finset Edge} (hF : Inside V F) :
    ∑ z ∈ V.filter (fun z => ¬ Black z), deg F z = F.card := by sorry
