-- Prove2me | Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3
-- name    : P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:40.483689+00:00
-- url     : https://prove2.me/theorems/3c85acea-6199-5329-9754-242fb8ef4e1c
-- title:
--   P2 M Tunnell Map Orthogonal Frame e  orthogonal 756a68c1a1d3: P2 M Tunnell Map Orthogonal Frame e  orthogonal 756a68c1a1d3
-- statement:
--   The P2 M Tunnell Map Orthogonal Frame e  orthogonal 756a68c1a1d3 construction uses the P2 M Tunnell Map Orthogonal Frame e  orthogonal 756a68c1a1d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L109-L114
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L109-L114

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3 : dot p F.e₂ = 0 := by sorry

alias «TunnellMap».«OrthogonalFrame».«e₂_orthogonal» := P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3
