-- Prove2me | Theorems.Thm_TunnellMap_frame_span_unique
-- name    : TunnellMap.frame_span_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:00:46.784152+00:00
-- url     : https://prove2.me/theorems/dc95a1b4-0c3b-4714-bb6b-f8e3086faf03
-- title:
--   Tunnell Map: frame span unique
-- statement:
--   The Tunnell Map construction uses the frame span unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L178-L185
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L178-L185

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.frame_span_unique {r : Triple} (hr : dot p r = 0) :
    ∃! ab : ℤ × ℤ, r = span2 ab.1 ab.2 F.e₁ F.e₂ := by sorry
