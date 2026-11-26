-- Prove2me | Theorems.Thm_TunnellMap_targetLiftSign_eq_aResidualSign
-- name    : TunnellMap.targetLiftSign_eq_aResidualSign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:02:08.920573+00:00
-- url     : https://prove2.me/theorems/355fb15e-bd02-5bb8-9945-83669a0ff9b7
-- title:
--   Tunnell Map: target Lift Sign eq a Residual Sign
-- statement:
--   The Tunnell Map construction uses the target Lift Sign eq a Residual Sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L303-L316
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L303-L316

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.targetLiftSign_eq_aResidualSign {n : ℤ} (hnpos : 0 < n)
    (y : AResidual n) :
    targetLiftSign (residualTargetLift y) = aResidualSign hnpos y := by sorry
