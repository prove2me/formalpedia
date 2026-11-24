-- Prove2me | Theorems.Thm_ULHC_TF_ends_iff
-- name    : ULHC.TF.ends_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:45:28.086071+00:00
-- url     : https://prove2.me/theorems/1795603f-8c64-444b-b286-3a7bbf4cd206
-- title:
--   TF: ends iff
-- statement:
--   The TF construction uses the ends iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L160-L167
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L160-L167

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.ends_iff {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) (z : Pt) :
    (e.p = z ∨ e.q = z) ↔ (z = v ∨ z = other e v) := by sorry
