-- Prove2me | Theorems.Thm_ULHC_strip_odd
-- name    : ULHC.strip_odd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:33:49.252918+00:00
-- url     : https://prove2.me/theorems/669c7edf-e7a5-49ec-a5ef-95f4bc91baf5
-- title:
--   ULHC: strip odd
-- statement:
--   The ULHC construction uses the strip odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L459-L555
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L459-L555

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}

theorem ULHC.strip_odd : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2 V F →
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    ¬ Conn F (back1 c s) (front1 c s) → ncomp V (flipCol F c s (k + 1)) + 1 = ncomp V F ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 1)) x y ↔ Conn F x y ∨
          (Conn F x (back1 c s) ∧ Conn F (front1 c s) y) ∨
          (Conn F x (front1 c s) ∧ Conn F (back1 c s) y)) := by sorry
