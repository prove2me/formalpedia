-- Prove2me | Theorems.Thm_TunnellMap_lgSelect_reduced
-- name    : TunnellMap.lgSelect_reduced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:00:20.987829+00:00
-- url     : https://prove2.me/theorems/6ae64650-4b65-4c4e-9411-dd8348afb0a8
-- title:
--   Tunnell Map: lg Select reduced
-- statement:
--   The Tunnell Map construction uses the lg Select reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L271-L279
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L271-L279

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.lgSelect_reduced {uv : Triple × Triple} (h : IsReducedPair uv) :
    IsReducedPair (lgSelect uv) := by sorry
