-- Prove2me | Theorems.Thm_TunnellMap_aResidualSign_signAct
-- name    : TunnellMap.aResidualSign_signAct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:02:14.180199+00:00
-- url     : https://prove2.me/theorems/c75b4732-3bb5-40c0-81a0-8f0cac961f4d
-- title:
--   Tunnell Map: a Residual Sign sign Act
-- statement:
--   The Tunnell Map construction uses the a Residual Sign sign Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L259-L264
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L259-L264

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.aResidualSign_signAct {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (o : (aResidualInvolution n hnpos).Orbit) :
    aResidualSign hnpos
        (signActA hnpos σ (canonicalAResidualRepresentative hnpos o)) = σ := by sorry
