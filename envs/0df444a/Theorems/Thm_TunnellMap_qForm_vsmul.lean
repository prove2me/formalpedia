-- Prove2me | Theorems.Thm_TunnellMap_qForm_vsmul
-- name    : TunnellMap.qForm_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:39.460971+00:00
-- url     : https://prove2.me/theorems/5bf8795e-57e8-5696-9427-54a3f762c2bf
-- title:
--   Tunnell Map: q Form vsmul
-- statement:
--   The Tunnell Map construction uses the q Form vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L13-L16
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L13-L16

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_MidpointBound
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_vsmul (a : ℤ) (p : Triple) :
    qForm (vsmul a p) = a ^ 2 * qForm p := by sorry
