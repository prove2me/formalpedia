-- Prove2me | Theorems.Thm_ULHC_back1_nb
-- name    : ULHC.back1_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:26.420472+00:00
-- url     : https://prove2.me/theorems/2de38abe-94a2-4061-b563-e80e50cc4f39
-- title:
--   ULHC: back1 nb
-- statement:
--   The ULHC construction uses the back1 nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L101-L102
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L101-L102

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.back1_nb : back1 (nb c s) s = front1 c s := by sorry
