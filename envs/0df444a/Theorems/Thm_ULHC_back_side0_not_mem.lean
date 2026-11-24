-- Prove2me | Theorems.Thm_ULHC_back_side0_not_mem
-- name    : ULHC.back_side0_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:00:56.022771+00:00
-- url     : https://prove2.me/theorems/61ee375a-f3c5-4e2b-8029-a90e6f9e6d5e
-- title:
--   ULHC: back side0 not mem
-- statement:
--   The ULHC construction uses the back side0 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L99-L101
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L99-L101

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.back_side0_not_mem (c : Pt) (s : Side) (i : ℕ) :
    back (nb c (latA s)) s ∉ cellE (cellJ c s i) := by sorry
