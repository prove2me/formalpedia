-- Prove2me | Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
-- name    : P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:16.029205+00:00
-- url     : https://prove2.me/theorems/ca349fd7-00c2-4432-a275-a30e0580f028
-- title:
--   P2 M Tunnell Map orthogonal Frame Exec e  63bfe0839bbf: P2 M Tunnell Map orthogonal Frame Exec e  63bfe0839bbf
-- statement:
--   The P2 M Tunnell Map orthogonal Frame Exec e  63bfe0839bbf construction uses the P2 M Tunnell Map orthogonal Frame Exec e  63bfe0839bbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L130-L131
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L130-L131

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap

theorem P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).e₁ = frameE₁ p := by sorry

alias «TunnellMap».«orthogonalFrameExec_e₁» := P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf

attribute [defeq] P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
