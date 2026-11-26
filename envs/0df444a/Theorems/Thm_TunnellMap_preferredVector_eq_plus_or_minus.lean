-- Prove2me | Theorems.Thm_TunnellMap_preferredVector_eq_plus_or_minus
-- name    : TunnellMap.preferredVector_eq_plus_or_minus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:26.428584+00:00
-- url     : https://prove2.me/theorems/fa0274e2-4812-5fbf-8e3b-c3672e6a3f51
-- title:
--   Tunnell Map: preferred Vector eq plus or minus
-- statement:
--   The Tunnell Map construction uses the preferred Vector eq plus or minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L230-L234
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L230-L234

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.preferredVector_eq_plus_or_minus {n : ℤ} (s : BResidual n) (t : AResidual n) :
    preferredVector s t = plusVector s t ∨ preferredVector s t = minusVector s t := by sorry
