-- Prove2me | Theorems.Thm_ULHC_MP_amin_srcF_sound
-- name    : ULHC.MP.amin_srcF_sound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:13.243911+00:00
-- url     : https://prove2.me/theorems/6b1da614-6fbc-4d40-8205-e855d0c5e992
-- title:
--   MP: amin src F sound
-- statement:
--   The MP construction uses the amin src F sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L452-L464
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L452-L464

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.amin_srcF_sound {r : ℕ × List α}
    (h : amin (srcF NL src mid tgt edge w) NL = some r) :
    r.1 = pw w r.2 ∧ IsPath src mid tgt edge r.2 ∧ ∀ z ∈ r.2, z ∈ NL := by sorry
