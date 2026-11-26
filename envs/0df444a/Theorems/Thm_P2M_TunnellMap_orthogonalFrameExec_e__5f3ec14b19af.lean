-- Prove2me | Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
-- name    : P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:21.298925+00:00
-- url     : https://prove2.me/theorems/4729ec38-1d4a-43bf-a505-6072b69b63ef
-- title:
--   P2 M Tunnell Map orthogonal Frame Exec e  5f3ec14b19af: P2 M Tunnell Map orthogonal Frame Exec e  5f3ec14b19af
-- statement:
--   The P2 M Tunnell Map orthogonal Frame Exec e  5f3ec14b19af construction uses the P2 M Tunnell Map orthogonal Frame Exec e  5f3ec14b19af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L133-L134
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeterministicFrame.lean#L133-L134

import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_DeterministicFrame
set_option autoImplicit true
open TunnellMap

theorem P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).e₂ = frameE₂ p := by sorry

alias «TunnellMap».«orthogonalFrameExec_e₂» := P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af

attribute [defeq] P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
