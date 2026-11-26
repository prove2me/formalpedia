-- Prove2me | Theorems.Thm_TunnellMap_orbit_signActA
-- name    : TunnellMap.orbit_signActA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:05:47.115018+00:00
-- url     : https://prove2.me/theorems/8b14562c-e541-4ec1-8939-8e947c106009
-- title:
--   Tunnell Map: orbit sign Act A
-- statement:
--   The Tunnell Map construction uses the orbit sign Act A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L271-L274
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L271-L274

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.orbit_signActA {n : ℤ} (hnpos : 0 < n) (σ : ℤ) (y : AResidual n) :
    (aResidualInvolution n hnpos).orbit (signActA hnpos σ y) =
      (aResidualInvolution n hnpos).orbit y := by sorry
