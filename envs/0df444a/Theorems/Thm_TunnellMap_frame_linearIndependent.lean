-- Prove2me | Theorems.Thm_TunnellMap_frame_linearIndependent
-- name    : TunnellMap.frame_linearIndependent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:00:27.745074+00:00
-- url     : https://prove2.me/theorems/ee5aa028-8855-5d54-ae8c-fa941094719a
-- title:
--   Tunnell Map: frame linear Independent
-- statement:
--   The two computed basis vectors are linearly independent over `ℤ`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L156-L164
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L156-L164

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.frame_linearIndependent {a b : ℤ}
    (h : span2 a b F.e₁ F.e₂ = ⟨0, 0, 0⟩) : a = 0 ∧ b = 0 := by sorry
