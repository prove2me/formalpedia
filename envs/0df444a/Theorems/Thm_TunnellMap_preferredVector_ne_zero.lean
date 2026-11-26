-- Prove2me | Theorems.Thm_TunnellMap_preferredVector_ne_zero
-- name    : TunnellMap.preferredVector_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:44.348325+00:00
-- url     : https://prove2.me/theorems/099c0f16-4e54-5d59-a696-c5613c063b37
-- title:
--   Tunnell Map: preferred Vector ne zero
-- statement:
--   The Tunnell Map construction uses the preferred Vector ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L236-L242
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L236-L242

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.preferredVector_ne_zero {n : ℤ} (s : BResidual n) (t : AResidual n) :
    preferredVector s t ≠ ⟨0, 0, 0⟩ := by sorry
