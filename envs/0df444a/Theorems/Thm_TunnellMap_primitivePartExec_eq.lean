-- Prove2me | Theorems.Thm_TunnellMap_primitivePartExec_eq
-- name    : TunnellMap.primitivePartExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:58.472509+00:00
-- url     : https://prove2.me/theorems/90ec00cc-ce9f-4ee1-a56c-75952109a952
-- title:
--   Tunnell Map: primitive Part Exec eq
-- statement:
--   The Tunnell Map construction uses the primitive Part Exec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L85-L96
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L85-L96

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitivePartExec_eq {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartExec v = primitivePartTriple v := by sorry
