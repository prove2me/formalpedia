-- Prove2me | Theorems.Thm_TunnellMap_keyLtExec_iff
-- name    : TunnellMap.keyLtExec_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:20.290843+00:00
-- url     : https://prove2.me/theorems/96738260-8548-5501-a0db-06e2e5526d7f
-- title:
--   Tunnell Map: key Lt Exec iff
-- statement:
--   The Tunnell Map construction uses the key Lt Exec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L123-L125
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L123-L125

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.keyLtExec_iff (k₁ k₂ : DirectionKey) :
    keyLtExec k₁ k₂ = true ↔ k₁ < k₂ := by sorry
