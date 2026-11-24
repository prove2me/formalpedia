-- Prove2me | Theorems.Thm_ULHC_TF_other_other
-- name    : ULHC.TF.other_other
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:46:15.998985+00:00
-- url     : https://prove2.me/theorems/d00b5b70-6ccd-45b4-9d0c-8234647f0a78
-- title:
--   TF: other other
-- statement:
--   The TF construction uses the other other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L169-L175
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L169-L175

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.other_other {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) : other e (other e v) = v := by sorry
