-- Prove2me | Theorems.Thm_ULHC_D_flip_formula
-- name    : ULHC.D_flip_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:20.204159+00:00
-- url     : https://prove2.me/theorems/f47ff36a-7864-4e41-ba45-1acbe693afcd
-- title:
--   ULHC: D flip formula
-- statement:
--   The ULHC construction uses the D flip formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L256-L274
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L256-L274

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.D_flip_formula (F H : Finset Edge) (c x : Pt) :
    D (flip F c) H x - D F H x =
      (if c.2 = x.2 ∧ c.1 ≤ x.1 then - (if up F (lft c) then 2 else -2) else 0) +
      (if c.2 = x.2 ∧ c.1 < x.1 then - (if up F (rgt c) then 2 else -2) else 0) := by sorry
