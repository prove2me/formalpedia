-- Prove2me | Theorems.Thm_ULHC_MP_amin_srcF_le
-- name    : ULHC.MP.amin_srcF_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:23.072415+00:00
-- url     : https://prove2.me/theorems/b22b796b-3717-48a8-8acc-9a0d1bbad368
-- title:
--   MP: amin src F le
-- statement:
--   The MP construction uses the amin src F le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L469-L488
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L469-L488

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.amin_srcF_le {q : List α} (hq : IsPath src mid tgt edge q)
    (hqN : ∀ x ∈ q, x ∈ NL) :
    ∃ r, amin (srcF NL src mid tgt edge w) NL = some r ∧ r.1 ≤ pw w q := by sorry
