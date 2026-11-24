-- Prove2me | Theorems.Thm_ULHC_alt_of_lats
-- name    : ULHC.alt_of_lats
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:53:53.011234+00:00
-- url     : https://prove2.me/theorems/04689f94-d2fc-43f8-9dfc-1b2551939c47
-- title:
--   ULHC: alt of lats
-- statement:
--   The ULHC construction uses the alt of lats property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L120-L124
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L120-L124

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.alt_of_lats {F : Finset Edge} {u : Pt} {tf : Side} (l1 : lat1 u tf ∈ F) (l2 : lat2 u tf ∈ F)
    (b : back u tf ∉ F) (f : front u tf ∉ F) : Alt F u := by sorry
