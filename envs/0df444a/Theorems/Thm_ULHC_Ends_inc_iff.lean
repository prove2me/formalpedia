-- Prove2me | Theorems.Thm_ULHC_Ends_inc_iff
-- name    : ULHC.Ends.inc_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:03.608423+00:00
-- url     : https://prove2.me/theorems/4eff1467-a76a-4acb-b719-dacc7017061d
-- title:
--   Ends: inc iff
-- statement:
--   The Ends construction uses the inc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L29-L31
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L29-L31

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}

theorem ULHC.Ends.inc_iff (h : Ends e u v) (z : Pt) : (e.p = z ∨ e.q = z) ↔ (z = u ∨ z = v) := by sorry
