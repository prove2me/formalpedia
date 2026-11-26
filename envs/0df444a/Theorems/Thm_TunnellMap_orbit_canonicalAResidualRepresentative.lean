-- Prove2me | Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
-- name    : TunnellMap.orbit_canonicalAResidualRepresentative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:04:06.292366+00:00
-- url     : https://prove2.me/theorems/21f77469-5b98-55f1-8e16-1b3ea10d97cf
-- title:
--   Tunnell Map: orbit canonical AResidual Representative
-- statement:
--   The Tunnell Map construction uses the orbit canonical AResidual Representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L189-L194
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L189-L194

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.orbit_canonicalAResidualRepresentative {n : ℤ} (hnpos : 0 < n)
    (o : (aResidualInvolution n hnpos).Orbit) :
    (aResidualInvolution n hnpos).orbit
      (canonicalAResidualRepresentative hnpos o) = o := by sorry
