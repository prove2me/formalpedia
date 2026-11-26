-- Prove2me | Theorems.Thm_TunnellMap_frame_change_unimodular
-- name    : TunnellMap.frame_change_unimodular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:03:50.873779+00:00
-- url     : https://prove2.me/theorems/6b2245cc-d317-5abd-9449-4168d53cb46b
-- title:
--   Tunnell Map: frame change unimodular
-- statement:
--   **The change of basis between any two frames of the same primitive source
--   is unimodular of determinant one.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L239-L264
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L239-L264

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F G : OrthogonalFrame p)

theorem TunnellMap.frame_change_unimodular (hp : p ≠ ⟨0, 0, 0⟩) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      G.e₁ = span2 a b F.e₁ F.e₂ ∧ G.e₂ = span2 c d F.e₁ F.e₂ := by sorry
