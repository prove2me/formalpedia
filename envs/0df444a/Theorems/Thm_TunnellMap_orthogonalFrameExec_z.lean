-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_z
-- name    : TunnellMap.orthogonalFrameExec_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:35.419081+00:00
-- url     : https://prove2.me/theorems/44a99a92-9f30-4c70-afe9-b6b5177ed0e6
-- title:
--   Tunnell Map: orthogonal Frame Exec z
-- statement:
--   The Tunnell Map construction uses the orthogonal Frame Exec z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L136-L137
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L136-L137

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.orthogonalFrameExec_z (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).z = tripleBezout p := by sorry

attribute [defeq] TunnellMap.orthogonalFrameExec_z
