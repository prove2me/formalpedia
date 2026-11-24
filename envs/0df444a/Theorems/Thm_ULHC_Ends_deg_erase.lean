-- Prove2me | Theorems.Thm_ULHC_Ends_deg_erase
-- name    : ULHC.Ends.deg_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:03.402022+00:00
-- url     : https://prove2.me/theorems/0d1a9c4c-1d63-4298-bc77-03513edafa0e
-- title:
--   Ends: deg erase
-- statement:
--   The Ends construction uses the deg erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L63-L68
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L63-L68

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_deg_erase

set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}

theorem ULHC.Ends.deg_erase {F : Finset Edge} (h : Ends e u v) (he : e ∈ F) (z : Pt) :
    deg (F.erase e) z + (if z = u ∨ z = v then 1 else 0) = deg F z := by sorry
