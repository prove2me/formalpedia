-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_gram_det
-- name    : TunnellMap.OrthogonalFrame.gram_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:48.862738+00:00
-- url     : https://prove2.me/theorems/8a1a31a6-0040-5376-8199-fe93b412f9f5
-- title:
--   Orthogonal Frame: gram det
-- statement:
--   The Orthogonal Frame construction uses the gram det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L116-L120
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L116-L120

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.gram_det :
    dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2 = dot p p := by sorry
