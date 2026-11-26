-- Prove2me | Theorems.Thm_TunnellMap_keyLeExec_iff
-- name    : TunnellMap.keyLeExec_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:34.882812+00:00
-- url     : https://prove2.me/theorems/aeed301c-9380-50f4-b55d-9be1a7892546
-- title:
--   Tunnell Map: key Le Exec iff
-- statement:
--   The Tunnell Map construction uses the key Le Exec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L130-L132
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L130-L132

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.keyLeExec_iff (k₁ k₂ : DirectionKey) :
    keyLeExec k₁ k₂ = true ↔ k₁ ≤ k₂ := by sorry
