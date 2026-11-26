-- Prove2me | Theorems.Thm_TunnellMap_signActB_neg_sign
-- name    : TunnellMap.signActB_neg_sign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:00:56.733921+00:00
-- url     : https://prove2.me/theorems/299a73cf-82dc-5e13-b90e-ffa73682bdfa
-- title:
--   Tunnell Map: sign Act B neg sign
-- statement:
--   The Tunnell Map construction uses the sign Act B neg sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L196-L198
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L196-L198

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signActB_neg_sign {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (x : BResidual n) :
    signActB (-σ) x = negBResidual (signActB σ x) := by sorry
