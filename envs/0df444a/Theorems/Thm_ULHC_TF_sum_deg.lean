-- Prove2me | Theorems.Thm_ULHC_TF_sum_deg
-- name    : ULHC.TF.sum_deg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:39:53.180903+00:00
-- url     : https://prove2.me/theorems/affeff6e-1596-4e87-9e04-a261c4b24842
-- title:
--   TF: sum deg
-- statement:
--   The TF construction uses the sum deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L302-L327
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L302-L327

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.sum_deg {S : Finset Pt} (hS : ∀ e : Edge, ¬ (e.p ∈ S ∧ e.q ∈ S)) (F : Finset Edge) :
    ∑ z ∈ S, deg F z = (F.filter (fun e => e.p ∈ S ∨ e.q ∈ S)).card := by sorry
