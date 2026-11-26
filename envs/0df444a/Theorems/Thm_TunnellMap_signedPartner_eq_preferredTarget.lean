-- Prove2me | Theorems.Thm_TunnellMap_signedPartner_eq_preferredTarget
-- name    : TunnellMap.signedPartner_eq_preferredTarget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:13:15.991243+00:00
-- url     : https://prove2.me/theorems/bc5eda61-099c-473f-9f2a-f7406a9332fc
-- title:
--   Tunnell Map: signed Partner eq preferred Target
-- statement:
--   The Tunnell Map construction uses the signed Partner eq preferred Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L420-L426
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L420-L426

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signedPartner_eq_preferredTarget {n : ℤ} (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    signedPartner hnpos s t = preferredTarget s t := by sorry
