-- Prove2me | Theorems.Thm_ULHC_link_step
-- name    : ULHC.link_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:51:13.866837+00:00
-- url     : https://prove2.me/theorems/fe94eb8b-1562-415a-b0c4-3da217cc1dc3
-- title:
--   ULHC: link step
-- statement:
--   The ULHC construction uses the link step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean#L76-L95
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean#L76-L95

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.link_step {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
    {b c : StripSpec} (hb : ValidStrip V G b) (hl : CR2 V G b c) : ValidStrip V (applyS G b) c := by sorry
