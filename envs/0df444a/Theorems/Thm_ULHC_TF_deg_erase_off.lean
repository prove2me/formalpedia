-- Prove2me | Theorems.Thm_ULHC_TF_deg_erase_off
-- name    : ULHC.TF.deg_erase_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:47:20.234669+00:00
-- url     : https://prove2.me/theorems/1e221e25-ec65-429a-bfd5-335e7af4362c
-- title:
--   TF: deg erase off
-- statement:
--   The TF construction uses the deg erase off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L288-L290
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L288-L290

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.deg_erase_off {F : Finset Edge} {e : Edge} (he : e ∈ F) {z : Pt} (hz : ¬ (e.p = z ∨ e.q = z)) :
    deg (F.erase e) z = deg F z := by sorry
