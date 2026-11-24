-- Prove2me | Theorems.Thm_ULHC_back_nb
-- name    : ULHC.back_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:25.51849+00:00
-- url     : https://prove2.me/theorems/df0c0810-40c0-449e-9175-d8b17db1c171
-- title:
--   ULHC: back nb
-- statement:
--   The ULHC construction uses the back nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L97-L99
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Strip.lean#L97-L99

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.back_nb : back (nb c s) s = front c s := by sorry
