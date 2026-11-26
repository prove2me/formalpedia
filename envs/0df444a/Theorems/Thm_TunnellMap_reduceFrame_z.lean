-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_z
-- name    : TunnellMap.reduceFrame_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:20.938471+00:00
-- url     : https://prove2.me/theorems/d574ead5-a77a-4a61-8dac-dabd2d7df244
-- title:
--   Tunnell Map: reduce Frame z
-- statement:
--   The Tunnell Map construction uses the reduce Frame z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L305-L306
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L305-L306

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_z (F : OrthogonalFrame p) :
    (reduceFrame F).z = F.z := by sorry

attribute [defeq] TunnellMap.reduceFrame_z
