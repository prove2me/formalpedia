-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_sign
-- name    : TunnellMap.FreeInvolution.signAct_neg_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:05:12.1267+00:00
-- url     : https://prove2.me/theorems/984522cf-70aa-5802-90c4-6fec10aaf270
-- title:
--   Free Involution: sign Act neg sign
-- statement:
--   The Free Involution construction uses the sign Act neg sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L53-L55
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L53-L55

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.signAct_neg_sign {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (x : X) :
    I.signAct (-σ) x = I.neg (I.signAct σ x) := by sorry
