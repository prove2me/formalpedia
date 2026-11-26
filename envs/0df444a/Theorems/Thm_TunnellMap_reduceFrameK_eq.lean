-- Prove2me | Theorems.Thm_TunnellMap_reduceFrameK_eq
-- name    : TunnellMap.reduceFrameK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:07.858482+00:00
-- url     : https://prove2.me/theorems/88677b1e-738e-5757-8e56-702a98af3297
-- title:
--   Tunnell Map: reduce Frame K eq
-- statement:
--   The Tunnell Map construction uses the reduce Frame K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L331-L334
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L331-L334

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.reduceFrameK_eq {p : Triple} (F : OrthogonalFrame p) :
    reduceFrameK F = reduceFrame F := by sorry
