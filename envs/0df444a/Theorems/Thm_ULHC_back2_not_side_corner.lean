-- Prove2me | Theorems.Thm_ULHC_back2_not_side_corner
-- name    : ULHC.back2_not_side_corner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:43:30.692483+00:00
-- url     : https://prove2.me/theorems/767aad19-a412-4614-bbff-932001860e1a
-- title:
--   ULHC: back2 not side corner
-- statement:
--   The ULHC construction uses the back2 not side corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L85-L89
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L85-L89

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.back2_not_side_corner :
    back2 c s ∉ ({back1 (nb c (latA s)) s, back2 (nb c (latA s)) s, front1 (nb c (latA s)) s,
      front2 (nb c (latA s)) s} : Finset Pt) := by sorry
