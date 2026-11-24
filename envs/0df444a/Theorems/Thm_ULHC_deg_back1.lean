-- Prove2me | Theorems.Thm_ULHC_deg_back1
-- name    : ULHC.deg_back1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:52:42.646195+00:00
-- url     : https://prove2.me/theorems/5fc7e591-312a-4310-9175-353c658a4f6a
-- title:
--   ULHC: deg back1
-- statement:
--   The ULHC construction uses the deg back1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L34-L40
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L34-L40

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.deg_back1 (F : Finset Edge) :
    deg F (back1 c s) =
      ind F (lat1 c s) + ind F (back c s) + ind F (lat1 (nb c s.opp) s) +
        ind F (back (nb c (latA s)) s) := by sorry
