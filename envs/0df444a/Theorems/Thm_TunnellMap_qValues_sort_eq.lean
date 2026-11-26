-- Prove2me | Theorems.Thm_TunnellMap_qValues_sort_eq
-- name    : TunnellMap.qValues_sort_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:36:03.064522+00:00
-- url     : https://prove2.me/theorems/dc6321fc-9cb4-46cc-9a7f-e104a28d6953
-- title:
--   Tunnell Map: q Values sort eq
-- statement:
--   The Tunnell Map construction uses the q Values sort eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L61-L67
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L61-L67

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.qValues_sort_eq (n A : ℤ) :
    (qValues n A).sort (· ≤ ·) = qValuesL n A := by sorry
