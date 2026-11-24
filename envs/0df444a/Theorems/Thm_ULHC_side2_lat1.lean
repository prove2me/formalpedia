-- Prove2me | Theorems.Thm_ULHC_side2_lat1
-- name    : ULHC.side2_lat1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:57:00.059723+00:00
-- url     : https://prove2.me/theorems/9d625aef-76a4-49a6-aa46-d51b4b659e6e
-- title:
--   ULHC: side2 lat1
-- statement:
--   The ULHC construction uses the side2 lat1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L65-L67
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L65-L67

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.side2_lat1 : lat1 (nb c (latB s)) s = lat2 c s := by sorry
