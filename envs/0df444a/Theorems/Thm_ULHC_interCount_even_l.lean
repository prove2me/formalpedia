-- Prove2me | Theorems.Thm_ULHC_interCount_even_l
-- name    : ULHC.interCount_even_l
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:50:55.600324+00:00
-- url     : https://prove2.me/theorems/e6f32ac3-84fb-4ea0-b38b-f1826307d0ff
-- title:
--   ULHC: inter Count even l
-- statement:
--   The ULHC construction uses the inter Count even l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L171-L241
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L171-L241

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F)
include hF

theorem ULHC.interCount_even_l {w : Pt} (hw : IsCell V w) (hTw : NotTypeIII V F w)
    (hTn : ∀ s, Inter V F (sideEdge w s) → IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    interCount V F w % 2 = 0 := by sorry
