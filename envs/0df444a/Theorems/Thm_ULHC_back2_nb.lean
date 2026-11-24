-- Prove2me | Theorems.Thm_ULHC_back2_nb
-- name    : ULHC.back2_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:56.968826+00:00
-- url     : https://prove2.me/theorems/79130597-ab50-4977-bcc5-b4e8664bc005
-- title:
--   ULHC: back2 nb
-- statement:
--   The ULHC construction uses the back2 nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L104-L105
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L104-L105

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.back2_nb : back2 (nb c s) s = front2 c s := by sorry
