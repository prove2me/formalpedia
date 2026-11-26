-- Prove2me | Theorems.Thm_TunnellMap_minusVector_ne_zero
-- name    : TunnellMap.minusVector_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:03.751096+00:00
-- url     : https://prove2.me/theorems/f486647e-91fb-5ff7-a48a-6c66694baafc
-- title:
--   Tunnell Map: minus Vector ne zero
-- statement:
--   The Tunnell Map construction uses the minus Vector ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L179-L185
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L179-L185

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.minusVector_ne_zero {n : ℤ} (s : BResidual n) (t : AResidual n) :
    minusVector s t ≠ ⟨0, 0, 0⟩ := by sorry
