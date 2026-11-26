-- Prove2me | Theorems.Thm_TunnellMap_frame_gram_det
-- name    : TunnellMap.frame_gram_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:50.108169+00:00
-- url     : https://prove2.me/theorems/f660a834-f5c0-48f5-914c-95e2cdd0a37f
-- title:
--   Tunnell Map: frame gram det
-- statement:
--   The Gram determinant of the computed basis is the norm of the source
--   vector, as required by the manuscript.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L189-L190
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L189-L190

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.frame_gram_det :
    dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2 = dot p p := by sorry
