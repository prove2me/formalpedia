-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirectionExec_vsmul_pos
-- name    : TunnellMap.primitiveDirectionExec_vsmul_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:28:24.331734+00:00
-- url     : https://prove2.me/theorems/fa472f83-eae7-5e14-bf9a-91b76694236b
-- title:
--   Tunnell Map: primitive Direction Exec vsmul pos
-- statement:
--   The Tunnell Map construction uses the primitive Direction Exec vsmul pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L167-L170
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L167-L170

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirectionExec_vsmul_pos {c : ℤ} (hc : 0 < c) (v : Triple) :
    primitiveDirectionExec (vsmul c v) = primitiveDirectionExec v := by sorry
