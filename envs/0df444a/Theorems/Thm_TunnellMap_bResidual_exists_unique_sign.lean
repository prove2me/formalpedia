-- Prove2me | Theorems.Thm_TunnellMap_bResidual_exists_unique_sign
-- name    : TunnellMap.bResidual_exists_unique_sign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:01:31.133579+00:00
-- url     : https://prove2.me/theorems/32cf1f40-495d-4767-859a-20748f65b5d6
-- title:
--   Tunnell Map: b Residual exists unique sign
-- statement:
--   **Unique canonical decomposition of a residual source point.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L224-L229
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L224-L229

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.bResidual_exists_unique_sign (x : BResidual n) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      signActB σ
        (canonicalBResidualRepresentative ((bResidualInvolution n).orbit x)) = x := by sorry
