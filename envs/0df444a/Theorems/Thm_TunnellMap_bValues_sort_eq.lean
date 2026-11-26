-- Prove2me | Theorems.Thm_TunnellMap_bValues_sort_eq
-- name    : TunnellMap.bValues_sort_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:35:27.817944+00:00
-- url     : https://prove2.me/theorems/638bdbd2-6323-5f5c-918e-f7b69e432f91
-- title:
--   Tunnell Map: b Values sort eq
-- statement:
--   The Tunnell Map construction uses the b Values sort eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L91-L93
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L91-L93

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.bValues_sort_eq {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : (bValues n F A q).sort (· ≤ ·) = bValuesL n F A q := by sorry
