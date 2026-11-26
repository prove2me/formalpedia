-- Prove2me | Theorems.Thm_TunnellMap_qBilinear_vsmul_vsmul
-- name    : TunnellMap.qBilinear_vsmul_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:50.569847+00:00
-- url     : https://prove2.me/theorems/b7a8480c-7d40-432a-add4-ef1bf32d4af0
-- title:
--   Tunnell Map: q Bilinear vsmul vsmul
-- statement:
--   The Tunnell Map construction uses the q Bilinear vsmul vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L50-L53
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L50-L53

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qBilinear_vsmul_vsmul (a b : ℤ) (p : Triple) :
    qBilinear (vsmul a p) (vsmul b p) = a * b * qForm p := by sorry
