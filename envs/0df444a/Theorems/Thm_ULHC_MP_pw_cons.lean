-- Prove2me | Theorems.Thm_ULHC_MP_pw_cons
-- name    : ULHC.MP.pw_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:31.706947+00:00
-- url     : https://prove2.me/theorems/df82cc95-d46a-49dd-bdc6-30426123bba2
-- title:
--   MP: pw cons
-- statement:
--   The MP construction uses the pw cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L116-L117
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L116-L117

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.pw_cons (x : α) (L : List α) : pw w (x :: L) = w x + pw w L := by sorry
