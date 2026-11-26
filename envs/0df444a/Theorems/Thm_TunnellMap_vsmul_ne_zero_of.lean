-- Prove2me | Theorems.Thm_TunnellMap_vsmul_ne_zero_of
-- name    : TunnellMap.vsmul_ne_zero_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:41.69109+00:00
-- url     : https://prove2.me/theorems/dc3660b2-17a5-55f4-a5f4-73d4e8b0cbe5
-- title:
--   Tunnell Map: vsmul ne zero of
-- statement:
--   The Tunnell Map construction uses the vsmul ne zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L172-L182
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L172-L182

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.vsmul_ne_zero_of {c : ℤ} (hc : c ≠ 0) {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    vsmul c v ≠ ⟨0, 0, 0⟩ := by sorry
