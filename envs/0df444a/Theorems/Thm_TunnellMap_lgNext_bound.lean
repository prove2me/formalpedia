-- Prove2me | Theorems.Thm_TunnellMap_lgNext_bound
-- name    : TunnellMap.lgNext_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:59:44.017742+00:00
-- url     : https://prove2.me/theorems/cc5a0651-2652-4a24-b34d-fa3bf46f07bb
-- title:
--   Tunnell Map: lg Next bound
-- statement:
--   **The Lagrange-Gauss size-reduction inequality.**  After one reduction
--   step the mixed term is at most half the first square length.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L144-L154
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L144-L154

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.lgNext_bound (u v : Triple) : |2 * dot u (lgNext u v)| ≤ dot u u := by sorry
