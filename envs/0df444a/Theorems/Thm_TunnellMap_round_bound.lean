-- Prove2me | Theorems.Thm_TunnellMap_round_bound
-- name    : TunnellMap.round_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:57:59.644118+00:00
-- url     : https://prove2.me/theorems/46389aaf-b576-5166-9016-e8d733a7046d
-- title:
--   Tunnell Map: round bound
-- statement:
--   The nearest-integer rounding bound, with ties rounded toward zero.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L100-L117
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L100-L117

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.round_bound {a b : ℤ} (ha : 0 < a) :
    -a ≤ 2 * (b - nearestQuot b a * a) ∧ 2 * (b - nearestQuot b a * a) ≤ a := by sorry
