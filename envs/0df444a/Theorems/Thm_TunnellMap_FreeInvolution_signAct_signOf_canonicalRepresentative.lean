-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_signOf_canonicalRepresentative
-- name    : TunnellMap.FreeInvolution.signAct_signOf_canonicalRepresentative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:06:50.134848+00:00
-- url     : https://prove2.me/theorems/f4db0f55-92b7-5961-9b6a-600fb53874f8
-- title:
--   Free Involution: sign Act sign Of canonical Representative
-- statement:
--   The Free Involution construction uses the sign Act sign Of canonical Representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L96-L101
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L96-L101

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.signAct_signOf_canonicalRepresentative (key : X → K)
    (hkey : Function.Injective key) (x : X) :
    I.signAct (I.signOf key x)
      (I.canonicalRepresentative key hkey (I.orbit x)) = x := by sorry
