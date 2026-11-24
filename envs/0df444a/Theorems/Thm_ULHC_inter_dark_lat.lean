-- Prove2me | Theorems.Thm_ULHC_inter_dark_lat
-- name    : ULHC.inter_dark_lat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:38:29.465882+00:00
-- url     : https://prove2.me/theorems/d8721406-1346-4387-aee7-2d72958c9ea9
-- title:
--   ULHC: inter dark lat
-- statement:
--   The ULHC construction uses the inter dark lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L68-L78
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L68-L78

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F)
include hF hT

theorem ULHC.inter_dark_lat {w : Pt} (hw : IsCell V w) (s : Side) (h : Inter V F (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by sorry
