-- Prove2me | Theorems.Thm_TunnellMap_directionKeyExec_eq
-- name    : TunnellMap.directionKeyExec_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:27:54.220836+00:00
-- url     : https://prove2.me/theorems/29169dd4-8045-565a-ab57-a35ae9140858
-- title:
--   Tunnell Map: direction Key Exec eq
-- statement:
--   The Tunnell Map construction uses the direction Key Exec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L138-L140
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L138-L140

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.directionKeyExec_eq {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKeyExec v = directionKey v := by sorry
