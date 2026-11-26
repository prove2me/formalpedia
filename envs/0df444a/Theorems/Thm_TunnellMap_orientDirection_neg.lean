-- Prove2me | Theorems.Thm_TunnellMap_orientDirection_neg
-- name    : TunnellMap.orientDirection_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:52.09706+00:00
-- url     : https://prove2.me/theorems/6146d6fa-89c3-46ff-a2ff-ec110f04de2a
-- title:
--   Tunnell Map: orient Direction neg
-- statement:
--   The Tunnell Map construction uses the orient Direction neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L256-L264
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L256-L264

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.orientDirection_neg {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    orientDirection (negTriple v) = orientDirection v := by sorry
