-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg
-- name    : TunnellMap.FreeInvolution.signAct_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:00:35.593898+00:00
-- url     : https://prove2.me/theorems/a783f1cb-0f1e-4b56-8cd4-a1b2f244a1c4
-- title:
--   Free Involution: sign Act neg
-- statement:
--   The Free Involution construction uses the sign Act neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L44-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L44-L46

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.signAct_neg (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (x : X) :
    I.signAct σ (I.neg x) = I.signAct (-σ) x := by sorry
