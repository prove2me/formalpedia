-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirectionExec_eq
-- name    : TunnellMap.primitiveDirectionExec_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:27:52.770005+00:00
-- url     : https://prove2.me/theorems/f00e6191-60e2-5a0c-b645-85467fb19037
-- title:
--   Tunnell Map: primitive Direction Exec eq
-- statement:
--   The Tunnell Map construction uses the primitive Direction Exec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L102-L104
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L102-L104

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirectionExec_eq {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirectionExec v = primitiveDirection v := by sorry
