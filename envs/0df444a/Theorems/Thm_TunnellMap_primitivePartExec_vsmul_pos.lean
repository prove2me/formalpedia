-- Prove2me | Theorems.Thm_TunnellMap_primitivePartExec_vsmul_pos
-- name    : TunnellMap.primitivePartExec_vsmul_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:22.835153+00:00
-- url     : https://prove2.me/theorems/5544ae34-1dbb-487d-9f52-f56872328b0f
-- title:
--   Tunnell Map: primitive Part Exec vsmul pos
-- statement:
--   The Tunnell Map construction uses the primitive Part Exec vsmul pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L160-L165
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L160-L165

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitivePartExec_vsmul_pos {c : ℤ} (hc : 0 < c) (v : Triple) :
    primitivePartExec (vsmul c v) = primitivePartExec v := by sorry
