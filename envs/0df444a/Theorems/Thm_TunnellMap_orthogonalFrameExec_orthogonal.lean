-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_orthogonal
-- name    : TunnellMap.orthogonalFrameExec_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:00.839621+00:00
-- url     : https://prove2.me/theorems/dd66a309-c810-49e3-a5ba-d58f0d6cc20e
-- title:
--   Tunnell Map: orthogonal Frame Exec orthogonal
-- statement:
--   Both computed basis vectors are integral and orthogonal to the source.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L201-L203
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L201-L203

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple}

theorem TunnellMap.orthogonalFrameExec_orthogonal (hp : tripleGCD p = 1) :
    dot p (frameE₁ p) = 0 ∧ dot p (frameE₂ p) = 0 := by sorry
