-- Prove2me | Theorems.Thm_TunnellMap_signedPartner_neg_target
-- name    : TunnellMap.signedPartner_neg_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:13:45.754139+00:00
-- url     : https://prove2.me/theorems/7ff5e1dd-a48b-4935-b6ef-852ee656e231
-- title:
--   Tunnell Map: signed Partner neg target
-- statement:
--   The Tunnell Map construction uses the signed Partner neg target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L428-L435
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L428-L435

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signedPartner_neg_target {n : ℤ} (hnpos : 0 < n) (s : BResidual n)
    (t : AResidual n) :
    signedPartner hnpos s (negAResidual t) = signedPartner hnpos s t := by sorry
