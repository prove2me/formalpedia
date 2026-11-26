-- Prove2me | Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a
-- name    : P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:14.036895+00:00
-- url     : https://prove2.me/theorems/ca2c7e05-3579-59c7-9d7e-120192a3a953
-- title:
--   P2 M Tunnell Map Orthogonal Frame e  orthogonal 6c82c70f8b3a: P2 M Tunnell Map Orthogonal Frame e  orthogonal 6c82c70f8b3a
-- statement:
--   The P2 M Tunnell Map Orthogonal Frame e  orthogonal 6c82c70f8b3a construction uses the P2 M Tunnell Map Orthogonal Frame e  orthogonal 6c82c70f8b3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L102-L107
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L102-L107

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a : dot p F.e₁ = 0 := by sorry

alias «TunnellMap».«OrthogonalFrame».«e₁_orthogonal» := P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a
