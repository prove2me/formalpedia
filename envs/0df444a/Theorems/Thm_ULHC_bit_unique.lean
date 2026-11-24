-- Prove2me | Theorems.Thm_ULHC_bit_unique
-- name    : ULHC.bit_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:40:54.637505+00:00
-- url     : https://prove2.me/theorems/d2217e4f-8457-462e-ad1e-f3a063523d37
-- title:
--   ULHC: bit unique
-- statement:
--   The ULHC construction uses the bit unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L631-L638
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L631-L638

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven

theorem ULHC.bit_unique {x0 z : Pt} {b1 b2 : Bool}
    (h1 : Relation.ReflTransGen (PStep V B) (x0, false) (z, b1))
    (h2 : Relation.ReflTransGen (PStep V B) (x0, false) (z, b2)) : b1 = b2 := by sorry
