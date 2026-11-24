-- Prove2me | Theorems.Thm_ULHC_alt_frame2
-- name    : ULHC.alt_frame2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:00:06.968792+00:00
-- url     : https://prove2.me/theorems/ae73927e-1c69-4072-86ad-d9cde630f745
-- title:
--   ULHC: alt frame2
-- statement:
--   The ULHC construction uses the alt frame2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L34-L48
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L34-L48

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.alt_frame2 {F : Finset Edge} {w : Pt} {tw : Side} (s : Side)
    (bw : back w tw ∈ F) (fw : front w tw ∈ F) (l1 : lat1 w tw ∉ F) (l2 : lat2 w tw ∉ F) :
    (back w s ∈ F ↔ front w s ∈ F) ∧ (lat1 w s ∈ F ↔ lat2 w s ∈ F) ∧
      (back w s ∈ F ↔ lat1 w s ∉ F) := by sorry
