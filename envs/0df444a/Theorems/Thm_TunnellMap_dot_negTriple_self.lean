-- Prove2me | Theorems.Thm_TunnellMap_dot_negTriple_self
-- name    : TunnellMap.dot_negTriple_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:58:18.163749+00:00
-- url     : https://prove2.me/theorems/94c0405f-c498-46ab-bf29-9dd4e2716b98
-- title:
--   Tunnell Map: dot neg Triple self
-- statement:
--   The Tunnell Map construction uses the dot neg Triple self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L65-L66
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L65-L66

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.dot_negTriple_self (u : Triple) : dot (negTriple u) (negTriple u) = dot u u := by sorry
