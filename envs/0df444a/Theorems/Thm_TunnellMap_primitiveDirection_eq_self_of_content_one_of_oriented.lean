-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented
-- name    : TunnellMap.primitiveDirection_eq_self_of_content_one_of_oriented
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:56.189999+00:00
-- url     : https://prove2.me/theorems/d1448639-c9db-4da9-b484-eb705497b838
-- title:
--   Tunnell Map: primitive Direction eq self of content one of oriented
-- statement:
--   The Tunnell Map construction uses the primitive Direction eq self of content one of oriented property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L287-L291
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L287-L291

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirection_eq_self_of_content_one_of_oriented {v : Triple}
    (hcontent : tripleContent v = 1) (horiented : FirstNonzeroPositive v) :
    primitiveDirection v = v := by sorry
