-- Prove2me | Theorems.Thm_TunnellMap_aResidual_exists_unique_sign
-- name    : TunnellMap.aResidual_exists_unique_sign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:01:59.458204+00:00
-- url     : https://prove2.me/theorems/33e6e299-aa17-453b-8615-561854620440
-- title:
--   Tunnell Map: a Residual exists unique sign
-- statement:
--   **Unique canonical decomposition of a residual target point.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L232-L238
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L232-L238

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.aResidual_exists_unique_sign {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      signActA hnpos σ
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y := by sorry
