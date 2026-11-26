-- Prove2me | Theorems.Thm_TunnellMap_frame_orthogonal
-- name    : TunnellMap.frame_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:53.738247+00:00
-- url     : https://prove2.me/theorems/73a01f94-9774-4e85-a66d-be1bf76dfb50
-- title:
--   Tunnell Map: frame orthogonal
-- statement:
--   Both computed basis vectors are orthogonal to the source vector.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L152-L153
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L152-L153

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.frame_orthogonal : dot p F.e₁ = 0 ∧ dot p F.e₂ = 0 := by sorry
