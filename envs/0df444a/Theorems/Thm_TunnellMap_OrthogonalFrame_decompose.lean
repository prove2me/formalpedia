-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_decompose
-- name    : TunnellMap.OrthogonalFrame.decompose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:24.778228+00:00
-- url     : https://prove2.me/theorems/ba8320d7-9010-4784-b302-efee805c7d4f
-- title:
--   Orthogonal Frame: decompose
-- statement:
--   The Orthogonal Frame construction uses the decompose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L128-L132
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L128-L132

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.decompose (r : Triple) :
    linComb3 (F.coeff₁ r) (F.coeff₂ r) (coeffZ (p := p) r) F.e₁ F.e₂ F.z = r := by sorry
