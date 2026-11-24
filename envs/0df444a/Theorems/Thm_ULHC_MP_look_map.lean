-- Prove2me | Theorems.Thm_ULHC_MP_look_map
-- name    : ULHC.MP.look_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:55.986918+00:00
-- url     : https://prove2.me/theorems/3ea30dec-e5c2-4346-9608-59b62cd5d21f
-- title:
--   MP: look map
-- statement:
--   The MP construction uses the look map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L268-L280
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L268-L280

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]

theorem ULHC.MP.look_map {β : Type} (x : α) (f : α → Option β) (l : List α) :
    look x (l.map (fun a => (a, f a))) = if x ∈ l then f x else none := by sorry
