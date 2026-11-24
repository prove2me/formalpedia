-- Prove2me | Theorems.Thm_ULHC_TF_other_black
-- name    : ULHC.TF.other_black
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:37.713553+00:00
-- url     : https://prove2.me/theorems/2e046304-ffc2-411b-9ea9-76af63dfffe3
-- title:
--   TF: other black
-- statement:
--   The TF construction uses the other black property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L177-L182
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L177-L182

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.other_black {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) :
    Black (other e v) ↔ ¬ Black v := by sorry
