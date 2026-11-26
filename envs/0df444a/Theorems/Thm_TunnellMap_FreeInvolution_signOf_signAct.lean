-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signOf_signAct
-- name    : TunnellMap.FreeInvolution.signOf_signAct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:59.684139+00:00
-- url     : https://prove2.me/theorems/d0cc69d7-c6a3-418c-9815-591a100478c4
-- title:
--   Free Involution: sign Of sign Act
-- statement:
--   The Free Involution construction uses the sign Of sign Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L145-L150
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L145-L150

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.signOf_signAct (key : X → K) (hkey : Function.Injective key)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (q : I.Orbit) :
    I.signOf key (I.signAct σ (I.canonicalRepresentative key hkey q)) = σ := by sorry
