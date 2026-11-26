-- Prove2me | Theorems.Thm_TunnellMap_rootValues_sort_eq
-- name    : TunnellMap.rootValues_sort_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:42:22.245875+00:00
-- url     : https://prove2.me/theorems/bff8f488-f373-44e6-89e6-8ac63a15b651
-- title:
--   Tunnell Map: root Values sort eq
-- statement:
--   The Tunnell Map construction uses the root Values sort eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L104-L140
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L104-L140

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.rootValues_sort_eq {p : Triple} (F : OrthogonalFrame p) (A q b : ℤ) :
    (rootValues F A q b).sort (· ≤ ·) = rootValuesL F A q b := by sorry
