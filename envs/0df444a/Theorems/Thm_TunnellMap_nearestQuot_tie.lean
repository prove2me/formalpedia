-- Prove2me | Theorems.Thm_TunnellMap_nearestQuot_tie
-- name    : TunnellMap.nearestQuot_tie
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:19.282564+00:00
-- url     : https://prove2.me/theorems/b1ef22df-1594-4804-bfe9-c7ca52030413
-- title:
--   Tunnell Map: nearest Quot tie
-- statement:
--   **Exact half-integer ties round toward zero.**  If `2 * b = (2 * k + 1) * a`
--   then `b / a` is the half-integer `k + 1/2`, and `nearestQuot b a` is `k` for a
--   nonnegative `b` and `k + 1` for a negative one — in both cases the nearer
--   integer to zero.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L123-L140
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L123-L140

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.nearestQuot_tie {a b k : ℤ} (ha : 0 < a) (h : 2 * b = (2 * k + 1) * a) :
    nearestQuot b a = if 0 ≤ b then k else k + 1 := by sorry
