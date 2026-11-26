-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
-- name    : TunnellMap.FreeInvolution.orbit_canonicalRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:10.630288+00:00
-- url     : https://prove2.me/theorems/e1cc1fc8-8849-5d84-94c8-2d9978e779da
-- title:
--   Free Involution: orbit canonical Representative
-- statement:
--   The Free Involution construction uses the orbit canonical Representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Antipodal.lean#L240-L247
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Antipodal.lean#L240-L247

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_Antipodal
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.orbit_canonicalRepresentative (key : X → K)
    (hkey : Function.Injective key) (q : I.Orbit) :
    I.orbit (I.canonicalRepresentative key hkey q) = q := by sorry
