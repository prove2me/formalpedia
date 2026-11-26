-- Prove2me | Theorems.Thm_TunnellMap_lgReduce_reduced
-- name    : TunnellMap.lgReduce_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:36.313132+00:00
-- url     : https://prove2.me/theorems/31be7900-1cb1-4b6e-b71d-181480de52ff
-- title:
--   Tunnell Map: lg Reduce reduced
-- statement:
--   The Tunnell Map construction uses the lg Reduce reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L281-L282
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L281-L282

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.lgReduce_reduced (u v : Triple) : IsReducedPair (lgReduce u v) := by sorry
