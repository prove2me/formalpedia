-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signOf_neg
-- name    : TunnellMap.FreeInvolution.signOf_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:10:36.707976+00:00
-- url     : https://prove2.me/theorems/3327c96e-a7e3-484f-95af-4a58f6bcd756
-- title:
--   Free Involution: sign Of neg
-- statement:
--   The Free Involution construction uses the sign Of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L118-L126
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L118-L126

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.signOf_neg (key : X → K) (hkey : Function.Injective key) (x : X) :
    I.signOf key (I.neg x) = - I.signOf key x := by sorry
