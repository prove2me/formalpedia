-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_lifts
-- name    : TunnellMap.Examples41.residual_lifts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:54:02.494896+00:00
-- url     : https://prove2.me/theorems/af60fb3c-b4cc-5bfb-a44f-1378acb1fe91
-- title:
--   Examples41: residual lifts
-- statement:
--   The Examples41 construction uses the residual lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L149-L159
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L149-L159

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_lifts :
    residualSourceLift s1 = ⟨-2, -5, -2⟩ ∧
      residualSourceLift s2 = ⟨-2, -5, 2⟩ ∧
      residualSourceLift s3 = ⟨-2, 5, -2⟩ ∧
      residualSourceLift s4 = ⟨-2, 5, 2⟩ ∧
      residualTargetLift t1 = ⟨-4, -3, 0⟩ ∧
      residualTargetLift t2 = ⟨-4, 3, 0⟩ ∧
      residualTargetLift t3 = ⟨0, -3, -4⟩ ∧
      residualTargetLift t4 = ⟨0, -3, 4⟩ := by sorry
