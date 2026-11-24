-- Prove2me | Theorems.Thm_ULHC_deg_back2
-- name    : ULHC.deg_back2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:53:00.457586+00:00
-- url     : https://prove2.me/theorems/000ec4e9-4ac9-4758-ad96-ec0f84ea246e
-- title:
--   ULHC: deg back2
-- statement:
--   The ULHC construction uses the deg back2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L51-L57
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L51-L57

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.deg_back2 (F : Finset Edge) :
    deg F (back2 c s) =
      ind F (lat2 c s) + ind F (back c s) + ind F (lat2 (nb c s.opp) s) +
        ind F (back (nb c (latB s)) s) := by sorry
