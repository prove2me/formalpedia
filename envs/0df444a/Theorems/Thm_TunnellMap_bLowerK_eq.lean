-- Prove2me | Theorems.Thm_TunnellMap_bLowerK_eq
-- name    : TunnellMap.bLowerK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:49.026368+00:00
-- url     : https://prove2.me/theorems/9a32bb96-563f-5f3e-8786-c2d92dd7a90c
-- title:
--   Tunnell Map: b Lower K eq
-- statement:
--   The Tunnell Map construction uses the b Lower K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L79-L81
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L79-L81

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.bLowerK_eq {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : bLowerK n F A q = bLower n F A q := by sorry
