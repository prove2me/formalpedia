-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirection_negTriple
-- name    : TunnellMap.primitiveDirection_negTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:49.580802+00:00
-- url     : https://prove2.me/theorems/83a4275e-dec4-5431-87ad-84c9b2be4926
-- title:
--   Tunnell Map: primitive Direction neg Triple
-- statement:
--   The Tunnell Map construction uses the primitive Direction neg Triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L299-L302
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L299-L302

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirection_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (negTriple v) = primitiveDirection v := by sorry
