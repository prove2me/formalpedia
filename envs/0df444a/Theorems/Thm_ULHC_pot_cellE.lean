-- Prove2me | Theorems.Thm_ULHC_pot_cellE
-- name    : ULHC.pot_cellE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:59.685798+00:00
-- url     : https://prove2.me/theorems/62e069a8-9bc7-45b5-aaae-93056003504d
-- title:
--   ULHC: pot cell E
-- statement:
--   The ULHC construction uses the pot cell E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L242-L252
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L242-L252

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.pot_cellE (c x : Pt) (f : Edge → ℤ) :
    pot (cellE c) f x =
      (if c.2 = x.2 ∧ c.1 ≤ x.1 then f (lft c) else 0) +
      (if c.2 = x.2 ∧ c.1 < x.1 then f (rgt c) else 0) := by sorry
