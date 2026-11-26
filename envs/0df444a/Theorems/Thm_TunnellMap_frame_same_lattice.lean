-- Prove2me | Theorems.Thm_TunnellMap_frame_same_lattice
-- name    : TunnellMap.frame_same_lattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:04:00.904673+00:00
-- url     : https://prove2.me/theorems/8fbcb0ae-88f0-5e3a-adbd-4ebe8ee1ab67
-- title:
--   Tunnell Map: frame same lattice
-- statement:
--   **Two frames of the same source span the same lattice.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L267-L269
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L267-L269

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F G : OrthogonalFrame p)

theorem TunnellMap.frame_same_lattice (r : Triple) :
    (∃ a b : ℤ, r = span2 a b F.e₁ F.e₂) ↔ (∃ a b : ℤ, r = span2 a b G.e₁ G.e₂) := by sorry
