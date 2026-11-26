-- Prove2me | Theorems.Thm_TunnellMap_signActA_neg_sign
-- name    : TunnellMap.signActA_neg_sign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:10:55.409014+00:00
-- url     : https://prove2.me/theorems/7ceb3637-c7e7-48a5-8fb0-3bf41a30667d
-- title:
--   Tunnell Map: sign Act A neg sign
-- statement:
--   The Tunnell Map construction uses the sign Act A neg sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L200-L203
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L200-L203

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signActA_neg_sign {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (y : AResidual n) :
    signActA hnpos (-σ) y = negAResidual (signActA hnpos σ y) := by sorry
