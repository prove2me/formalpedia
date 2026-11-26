-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_span_unique
-- name    : TunnellMap.orthogonalFrameExec_span_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:02:56.549783+00:00
-- url     : https://prove2.me/theorems/074c2ae1-6f1d-4879-8df9-cedf208448c2
-- title:
--   Tunnell Map: orthogonal Frame Exec span unique
-- statement:
--   The coefficients over the computed basis are unique.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L217-L220
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L217-L220

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple}

theorem TunnellMap.orthogonalFrameExec_span_unique (hp : tripleGCD p = 1) {r : Triple}
    (hr : dot p r = 0) :
    ∃! ab : ℤ × ℤ, r = span2 ab.1 ab.2 (frameE₁ p) (frameE₂ p) := by sorry
