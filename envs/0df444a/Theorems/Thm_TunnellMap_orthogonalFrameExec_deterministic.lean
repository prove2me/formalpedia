-- Prove2me | Theorems.Thm_TunnellMap_orthogonalFrameExec_deterministic
-- name    : TunnellMap.orthogonalFrameExec_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:21.762821+00:00
-- url     : https://prove2.me/theorems/430e862a-6773-4417-b607-702d492b78a0
-- title:
--   Tunnell Map: orthogonal Frame Exec deterministic
-- statement:
--   **Determinism.**  The computed frame does not depend on the proof of
--   primitivity, so repeated execution returns a definitionally identical
--   answer.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L142-L143
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L142-L143

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.orthogonalFrameExec_deterministic (p : Triple) (hp hp' : tripleGCD p = 1) :
    orthogonalFrameExec p hp = orthogonalFrameExec p hp' := by sorry
