-- Prove2me | Theorems.Thm_TunnellMap_signedPartner_signActA
-- name    : TunnellMap.signedPartner_signActA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:13:51.446826+00:00
-- url     : https://prove2.me/theorems/a85d713c-1788-4e35-8ab8-a1881a5fb108
-- title:
--   Tunnell Map: signed Partner sign Act A
-- statement:
--   The Tunnell Map construction uses the signed Partner sign Act A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L437-L443
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L437-L443

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signedPartner_signActA {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (s : BResidual n) (t : AResidual n) :
    signedPartner hnpos s (signActA hnpos σ t) = signedPartner hnpos s t := by sorry
