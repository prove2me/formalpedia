-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_inj_sign
-- name    : TunnellMap.FreeInvolution.signAct_inj_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:06:16.45271+00:00
-- url     : https://prove2.me/theorems/4c15005d-23e4-47b9-95e6-1e03ffaecf9f
-- title:
--   Free Involution: sign Act inj sign
-- statement:
--   Two signs acting equally on a point of a free involution are equal.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L65-L73
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L65-L73

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.signAct_inj_sign {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    {x : X} (h : I.signAct σ x = I.signAct τ x) : σ = τ := by sorry
