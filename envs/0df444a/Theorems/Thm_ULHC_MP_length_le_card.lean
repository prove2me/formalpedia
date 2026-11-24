-- Prove2me | Theorems.Thm_ULHC_MP_length_le_card
-- name    : ULHC.MP.length_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:48.358933+00:00
-- url     : https://prove2.me/theorems/b2096670-ec1a-4ce0-8c45-0f201577d989
-- title:
--   MP: length le card
-- statement:
--   The MP construction uses the length le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L171-L175
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L171-L175

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.length_le_card [DecidableEq α] {NL : List α} {l : List α} (hnd : l.Nodup)
    (hN : ∀ z ∈ l, z ∈ NL) : l.length ≤ NL.length := by sorry
