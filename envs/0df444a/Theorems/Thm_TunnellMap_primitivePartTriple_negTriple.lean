-- Prove2me | Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
-- name    : TunnellMap.primitivePartTriple_negTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:27.410769+00:00
-- url     : https://prove2.me/theorems/a33cec04-43e3-5f37-8c60-7249b35856e3
-- title:
--   Tunnell Map: primitive Part Triple neg Triple
-- statement:
--   The Tunnell Map construction uses the primitive Part Triple neg Triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L151-L155
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L151-L155

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitivePartTriple_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (negTriple v) = negTriple (primitivePartTriple v) := by sorry
