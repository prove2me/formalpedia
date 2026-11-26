-- Prove2me | Theorems.Thm_TunnellMap_dot_span2_left
-- name    : TunnellMap.dot_span2_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:54.560793+00:00
-- url     : https://prove2.me/theorems/aaf94a00-5c9f-47dc-a737-36dc415accf9
-- title:
--   Tunnell Map: dot span2 left
-- statement:
--   The Tunnell Map construction uses the dot span2 left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L46-L49
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L46-L49

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.dot_span2_left (p : Triple) {u v : Triple} (hu : dot p u = 0)
    (hv : dot p v = 0) (a b : ℤ) : dot p (span2 a b u v) = 0 := by sorry
