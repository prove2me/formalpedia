-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_linearIndependent
-- name    : TunnellMap.orthogonalFrameExec_linearIndependent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:02:18.725666+00:00
-- url     : https://prove2.me/theorems/bfff4d75-4bae-4bb9-944f-2d3794ff9184
-- title:
--   Tunnell Map: orthogonal Frame Exec linear Independent
-- statement:
--   The two computed basis vectors are linearly independent over `ℤ`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L206-L208
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L206-L208

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple}

theorem TunnellMap.orthogonalFrameExec_linearIndependent (hp : tripleGCD p = 1) {a b : ℤ}
    (h : span2 a b (frameE₁ p) (frameE₂ p) = ⟨0, 0, 0⟩) : a = 0 ∧ b = 0 := by sorry
