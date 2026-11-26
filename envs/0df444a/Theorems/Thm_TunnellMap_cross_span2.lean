-- Prove2me | Theorems.Thm_TunnellMap_cross_span2
-- name    : TunnellMap.cross_span2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:17.172808+00:00
-- url     : https://prove2.me/theorems/99b8d79f-97d0-5229-be55-23a78361d316
-- title:
--   Tunnell Map: cross span2
-- statement:
--   The Tunnell Map construction uses the cross span2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L42-L44
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L42-L44

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.cross_span2 (a b c d : ℤ) (u v : Triple) :
    cross (span2 a b u v) (span2 c d u v) = vsmul (a * d - b * c) (cross u v) := by sorry
