-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_gram_det
-- name    : TunnellMap.orthogonalFrameExec_gram_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:59.912134+00:00
-- url     : https://prove2.me/theorems/6690c81a-8c0e-4193-bcfc-f16583bf1aba
-- title:
--   Tunnell Map: orthogonal Frame Exec gram det
-- statement:
--   **The Gram determinant of the computed basis** is the norm of the source
--   vector required by the manuscript.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L224-L227
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L224-L227

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple}

theorem TunnellMap.orthogonalFrameExec_gram_det (hp : tripleGCD p = 1) :
    dot (frameE₁ p) (frameE₁ p) * dot (frameE₂ p) (frameE₂ p) -
      dot (frameE₁ p) (frameE₂ p) ^ 2 = dot p p := by sorry
