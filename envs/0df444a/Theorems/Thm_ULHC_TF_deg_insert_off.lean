-- Prove2me | Theorems.Thm_ULHC_TF_deg_insert_off
-- name    : ULHC.TF.deg_insert_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:47:41.833123+00:00
-- url     : https://prove2.me/theorems/384363ea-1638-4b3e-ab08-ca92528f4b6d
-- title:
--   TF: deg insert off
-- statement:
--   The TF construction uses the deg insert off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L296-L298
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L296-L298

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.deg_insert_off {F : Finset Edge} {e : Edge} (he : e ∉ F) {z : Pt} (hz : ¬ (e.p = z ∨ e.q = z)) :
    deg (insert e F) z = deg F z := by sorry
