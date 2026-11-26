-- Prove2me | Theorems.Thm_TunnellMap_OrthogonalFrame_det_eq_one
-- name    : TunnellMap.OrthogonalFrame.det_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:29.868939+00:00
-- url     : https://prove2.me/theorems/ef302bbd-01b2-5579-878b-df92836494ae
-- title:
--   Orthogonal Frame: det eq one
-- statement:
--   The Orthogonal Frame construction uses the det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L98-L100
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L98-L100

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)

theorem TunnellMap.OrthogonalFrame.det_eq_one : det3 F.e₁ F.e₂ F.z = 1 := by sorry
