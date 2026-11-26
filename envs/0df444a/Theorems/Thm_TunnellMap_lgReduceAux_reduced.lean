-- Prove2me | Theorems.Thm_TunnellMap_lgReduceAux_reduced
-- name    : TunnellMap.lgReduceAux_reduced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:58:31.204656+00:00
-- url     : https://prove2.me/theorems/5c282149-abc6-573d-9751-1eb6529434a4
-- title:
--   Tunnell Map: lg Reduce Aux reduced
-- statement:
--   The Tunnell Map construction uses the lg Reduce Aux reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L239-L246
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L239-L246

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.lgReduceAux_reduced (u v : Triple) : IsReducedPair (lgReduceAux u v) := by sorry
