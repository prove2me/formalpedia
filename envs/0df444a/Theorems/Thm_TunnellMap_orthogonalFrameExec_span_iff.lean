-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_span_iff
-- name    : TunnellMap.orthogonalFrameExec_span_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:03:42.915506+00:00
-- url     : https://prove2.me/theorems/7b0628c6-df35-46aa-b10f-9b15961a630b
-- title:
--   Tunnell Map: orthogonal Frame Exec span iff
-- statement:
--   **The computed pair spans every integral vector orthogonal to the
--   source.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L212-L214
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L212-L214

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple}

theorem TunnellMap.orthogonalFrameExec_span_iff (hp : tripleGCD p = 1) (r : Triple) :
    (∃ a b : ℤ, r = span2 a b (frameE₁ p) (frameE₂ p)) ↔ dot p r = 0 := by sorry
