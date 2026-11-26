-- Prove2me | Theorems.Thm_TunnellMap_content_mul_primitivePartTriple
-- name    : TunnellMap.content_mul_primitivePartTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:29.403362+00:00
-- url     : https://prove2.me/theorems/ba151c5b-8e31-44da-8f32-3760570f9595
-- title:
--   Tunnell Map: content mul primitive Part Triple
-- statement:
--   The coordinate form of `Polynomial.eq_C_content_mul_primPart`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L176-L187
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L176-L187

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.content_mul_primitivePartTriple (v : Triple) :
    v = vsmul (tripleContent v) (primitivePartTriple v) := by sorry
