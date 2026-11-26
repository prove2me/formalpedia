-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signOf_canonicalRepresentative
-- name    : TunnellMap.FreeInvolution.signOf_canonicalRepresentative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:03:53.688417+00:00
-- url     : https://prove2.me/theorems/9c32c293-31f0-4bae-8d88-d584f8d8c9c2
-- title:
--   Free Involution: sign Of canonical Representative
-- statement:
--   The Free Involution construction uses the sign Of canonical Representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L139-L143
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L139-L143

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.signOf_canonicalRepresentative (key : X → K)
    (hkey : Function.Injective key) (q : I.Orbit) :
    I.signOf key (I.canonicalRepresentative key hkey q) = 1 := by sorry
