-- Prove2me | Theorems.Thm_ULHC_T_layerT_time_le
-- name    : ULHC.T.layerT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:15:24.767045+00:00
-- url     : https://prove2.me/theorems/cc76cd89-eb92-4301-b457-76ad4a3fc7c0
-- title:
--   T: layer T time le
-- statement:
--   The T construction uses the layer T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L209-L217
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L209-L217

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.layerT_time_le : ∀ k, (layerT NL mid tgt edgeT w k).time ≤
    MP.layerCost NL mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time) k
  := by sorry
