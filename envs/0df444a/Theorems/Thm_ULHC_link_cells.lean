-- Prove2me | Theorems.Thm_ULHC_link_cells
-- name    : ULHC.link_cells
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:04.952556+00:00
-- url     : https://prove2.me/theorems/dd330bf8-7143-498f-ad29-5f5af63ee119
-- title:
--   ULHC: link cells
-- statement:
--   The ULHC construction uses the link cells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L170-L173
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L170-L173

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.link_cells {b c : StripSpec} (h : CR2 V G b c) :
    1 ≤ c.n ∧ ∀ j < c.n, IsCell V (cellJ c.c c.s j) := by sorry
