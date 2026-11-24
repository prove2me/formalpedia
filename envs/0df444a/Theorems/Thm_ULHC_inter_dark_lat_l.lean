-- Prove2me | Theorems.Thm_ULHC_inter_dark_lat_l
-- name    : ULHC.inter_dark_lat_l
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:50:55.939844+00:00
-- url     : https://prove2.me/theorems/3fe97414-acb9-4623-9b72-e618c3213b55
-- title:
--   ULHC: inter dark lat l
-- statement:
--   The ULHC construction uses the inter dark lat l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L158-L169
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L158-L169

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F)
include hF

theorem ULHC.inter_dark_lat_l {w : Pt} (hw : IsCell V w) (s : Side) (h : Inter V F (sideEdge w s))
    (hTr : IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by sorry
