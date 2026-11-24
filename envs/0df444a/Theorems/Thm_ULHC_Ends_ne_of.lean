-- Prove2me | Theorems.Thm_ULHC_Ends_ne_of
-- name    : ULHC.Ends.ne_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:07.326797+00:00
-- url     : https://prove2.me/theorems/1f6d0b3d-2ad8-480f-a280-534a55386460
-- title:
--   Ends: ne of
-- statement:
--   The Ends construction uses the ne of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L397-L403
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean#L397-L403

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.Ends.ne_of {e e' : Edge} {u v u' v' : Pt} (h : Ends e u v) (h' : Ends e' u' v')
    (h1 : v' ≠ u) (h2 : v' ≠ v) : e ≠ e' := by sorry
