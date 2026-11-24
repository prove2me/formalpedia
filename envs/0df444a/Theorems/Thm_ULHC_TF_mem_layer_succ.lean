-- Prove2me | Theorems.Thm_ULHC_TF_mem_layer_succ
-- name    : ULHC.TF.mem_layer_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:46:00.0577+00:00
-- url     : https://prove2.me/theorems/21826d3d-13b3-4717-a55a-d863675ad7ff
-- title:
--   TF: mem layer succ
-- statement:
--   The TF construction uses the mem layer succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L224-L226
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L224-L226

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.mem_layer_succ {V : Finset Pt} {F : Finset Edge} {k : ℕ} {v : Pt} :
    v ∈ layer V F (k + 1) ↔ v ∈ layer V F k ∨ ∃ u ∈ layer V F k, v ∈ nbr V F u := by sorry
