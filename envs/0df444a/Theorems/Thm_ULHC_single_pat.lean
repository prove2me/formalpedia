-- Prove2me | Theorems.Thm_ULHC_single_pat
-- name    : ULHC.single_pat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:22:36.468518+00:00
-- url     : https://prove2.me/theorems/bde9535f-a3a5-4989-a2d9-7efbeb1f9fe3
-- title:
--   ULHC: single pat
-- statement:
--   The ULHC construction uses the single pat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L24-L30
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L24-L30

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.single_pat {F : Finset Edge} {d : Pt} {tf : Side} (hb : back d tf ∈ F) (hl1 : lat1 d tf ∉ F)
    (hl2 : lat2 d tf ∉ F) (hf : front d tf ∈ F) : StripPat F d tf 1 := by sorry
