-- Prove2me | Theorems.Thm_ULHC_TF_deg_eq_card
-- name    : ULHC.TF.deg_eq_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:47:05.968121+00:00
-- url     : https://prove2.me/theorems/c03d8979-9ddc-4e99-9df9-77ace12d3ba9
-- title:
--   TF: deg eq card
-- statement:
--   The TF construction uses the deg eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L273-L282
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L273-L282

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.deg_eq_card (F : Finset Edge) (z : Pt) :
    deg F z = (F.filter (fun e => e.p = z ∨ e.q = z)).card := by sorry
