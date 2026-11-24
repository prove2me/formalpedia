-- Prove2me | Theorems.Thm_ULHC_TF_deg_erase_end
-- name    : ULHC.TF.deg_erase_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:47:13.239668+00:00
-- url     : https://prove2.me/theorems/f970bed8-7d41-4f18-b3e6-4c1202e350b6
-- title:
--   TF: deg erase end
-- statement:
--   The TF construction uses the deg erase end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L284-L286
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L284-L286

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.deg_erase_end {F : Finset Edge} {e : Edge} (he : e ∈ F) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    deg (F.erase e) z + 1 = deg F z := by sorry
