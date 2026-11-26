-- Prove2me | Theorems.Thm_TunnellMap_plusVector_ne_zero
-- name    : TunnellMap.plusVector_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:30.135928+00:00
-- url     : https://prove2.me/theorems/612caa8e-9c56-47c1-b1f4-0a0add1b3d53
-- title:
--   Tunnell Map: plus Vector ne zero
-- statement:
--   The Tunnell Map construction uses the plus Vector ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L171-L177
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L171-L177

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.plusVector_ne_zero {n : ℤ} (s : BResidual n) (t : AResidual n) :
    plusVector s t ≠ ⟨0, 0, 0⟩ := by sorry
