-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_exists_unique_sign
-- name    : TunnellMap.FreeInvolution.exists_unique_sign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:06:54.492543+00:00
-- url     : https://prove2.me/theorems/1ffe9603-e8a8-524e-8a26-842bb97b2c1a
-- title:
--   Free Involution: exists unique sign
-- statement:
--   **Unique signed decomposition.**  Every point of a free involution is the
--   canonical representative of its orbit, multiplied by a unique sign.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L105-L116
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L105-L116

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.exists_unique_sign (key : X → K) (hkey : Function.Injective key)
    (x : X) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      I.signAct σ (I.canonicalRepresentative key hkey (I.orbit x)) = x := by sorry
