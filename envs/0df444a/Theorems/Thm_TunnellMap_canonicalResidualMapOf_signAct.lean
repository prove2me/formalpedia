-- Prove2me | Theorems.Thm_TunnellMap_canonicalResidualMapOf_signAct
-- name    : TunnellMap.canonicalResidualMapOf_signAct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:13:41.811957+00:00
-- url     : https://prove2.me/theorems/cd015e19-91ba-59ac-9a24-9de60fd00c5e
-- title:
--   Tunnell Map: canonical Residual Map Of sign Act
-- statement:
--   **The literal pointwise sign-lift formula** `σ E ↦ σ η F`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L463-L472
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L463-L472

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.canonicalResidualMapOf_signAct {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    canonicalResidualMapOf hnpos M
        (signActB σ (canonicalBResidualRepresentative q)) =
      signActA hnpos (σ * canonicalEta hnpos q (M q))
        (canonicalAResidualRepresentative hnpos (M q)) := by sorry
