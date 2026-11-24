-- Prove2me | Theorems.Thm_ULHC_TF_layer_mono
-- name    : ULHC.TF.layer_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:46:29.896765+00:00
-- url     : https://prove2.me/theorems/bbb39194-a6bc-4c76-bc66-849439b99138
-- title:
--   TF: layer mono
-- statement:
--   The TF construction uses the layer mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L200-L204
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L200-L204

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.layer_mono {V : Finset Pt} {F : Finset Edge} {k j : ℕ} (h : k ≤ j) :
    layer V F k ⊆ layer V F j := by sorry
