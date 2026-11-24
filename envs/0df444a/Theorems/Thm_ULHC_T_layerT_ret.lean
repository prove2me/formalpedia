-- Prove2me | Theorems.Thm_ULHC_T_layerT_ret
-- name    : ULHC.T.layerT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:14:40.987419+00:00
-- url     : https://prove2.me/theorems/82b4f04c-90ed-4b09-a054-dbc4de5baa23
-- title:
--   T: layer T ret
-- statement:
--   The T construction uses the layer T ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L130-L134
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L130-L134

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.layerT_ret : ∀ k, (layerT NL mid tgt edgeT w k).ret =
    MP.layer NL mid tgt (fun a b => (edgeT a b).ret) w k
  := by sorry
