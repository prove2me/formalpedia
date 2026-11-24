-- Prove2me | Theorems.Thm_ULHC_TF_layer_sub_succ
-- name    : ULHC.TF.layer_sub_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:49.945652+00:00
-- url     : https://prove2.me/theorems/95d1301d-6a1b-4c57-89ac-72d111c1e385
-- title:
--   TF: layer sub succ
-- statement:
--   The TF construction uses the layer sub succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L196-L198
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L196-L198

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.layer_sub_succ {V : Finset Pt} {F : Finset Edge} {k : ℕ} :
    layer V F k ⊆ layer V F (k + 1) := by sorry
