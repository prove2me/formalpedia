-- Prove2me | Theorems.Thm_TunnellMap_signActB_neg_one
-- name    : TunnellMap.signActB_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:03:50.402659+00:00
-- url     : https://prove2.me/theorems/8e62dd3d-196a-5a16-986c-b2e29c6699ca
-- title:
--   Tunnell Map: sign Act B neg one
-- statement:
--   The Tunnell Map construction uses the sign Act B neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L171-L173
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L171-L173

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signActB_neg_one (x : BResidual n) :
    signActB (-1) x = negBResidual x := by sorry
