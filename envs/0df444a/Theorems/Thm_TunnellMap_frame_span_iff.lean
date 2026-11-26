-- Prove2me | Theorems.Thm_TunnellMap_frame_span_iff
-- name    : TunnellMap.frame_span_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:59:53.69229+00:00
-- url     : https://prove2.me/theorems/a6d32189-75a2-4934-a542-a6b2da54e3f4
-- title:
--   Tunnell Map: frame span iff
-- statement:
--   **The computed pair spans the whole orthogonal lattice**: an integral
--   vector is an integral combination of the two basis vectors exactly when it is
--   orthogonal to the source vector, and the coefficients are unique.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L169-L176
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L169-L176

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.frame_span_iff (r : Triple) :
    (∃ a b : ℤ, r = span2 a b F.e₁ F.e₂) ↔ dot p r = 0 := by sorry
