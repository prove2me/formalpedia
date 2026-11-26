-- Prove2me | Theorems.Thm_TunnellMap_primitivePartTriple_ne_zero
-- name    : TunnellMap.primitivePartTriple_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:15.205836+00:00
-- url     : https://prove2.me/theorems/7f183dbb-ebac-5161-b884-9498262f28d6
-- title:
--   Tunnell Map: primitive Part Triple ne zero
-- statement:
--   The Tunnell Map construction uses the primitive Part Triple ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L189-L195
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L189-L195

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitivePartTriple_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple v ≠ ⟨0, 0, 0⟩ := by sorry
