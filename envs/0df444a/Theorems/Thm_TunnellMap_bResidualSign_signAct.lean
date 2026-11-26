-- Prove2me | Theorems.Thm_TunnellMap_bResidualSign_signAct
-- name    : TunnellMap.bResidualSign_signAct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:12:05.653913+00:00
-- url     : https://prove2.me/theorems/26d8c14d-098d-4b06-8c49-f636678eb5c5
-- title:
--   Tunnell Map: b Residual Sign sign Act
-- statement:
--   The Tunnell Map construction uses the b Residual Sign sign Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L253-L257
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L253-L257

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.bResidualSign_signAct {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (q : (bResidualInvolution n).Orbit) :
    bResidualSign (signActB σ (canonicalBResidualRepresentative q)) = σ := by sorry
