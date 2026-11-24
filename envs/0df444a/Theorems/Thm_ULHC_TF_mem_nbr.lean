-- Prove2me | Theorems.Thm_ULHC_TF_mem_nbr
-- name    : ULHC.TF.mem_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:43.373339+00:00
-- url     : https://prove2.me/theorems/033463c2-802a-403a-9c32-cb3070204b8d
-- title:
--   TF: mem nbr
-- statement:
--   The TF construction uses the mem nbr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L189-L191
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L189-L191

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.mem_nbr {V : Finset Pt} {F : Finset Edge} {u v : Pt} :
    v ∈ nbr V F u ↔ ∃ e, (e.p = u ∨ e.q = u) ∧ Fwd V F u e ∧ other e u = v := by sorry
