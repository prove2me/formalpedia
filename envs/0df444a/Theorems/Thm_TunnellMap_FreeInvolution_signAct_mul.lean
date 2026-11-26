-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_mul
-- name    : TunnellMap.FreeInvolution.signAct_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:00:43.650039+00:00
-- url     : https://prove2.me/theorems/cedb20fc-6431-4058-aa8e-ac82d4087583
-- title:
--   Free Involution: sign Act mul
-- statement:
--   The Free Involution construction uses the sign Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L48-L51
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L48-L51

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.signAct_mul (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (x : X) : I.signAct σ (I.signAct τ x) = I.signAct (σ * τ) x := by sorry
