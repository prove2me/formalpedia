-- Prove2me | Theorems.Thm_TunnellMap_bUpperK_eq
-- name    : TunnellMap.bUpperK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:58.51304+00:00
-- url     : https://prove2.me/theorems/f824a902-1fe8-5fcc-993a-081aa8c90af1
-- title:
--   Tunnell Map: b Upper K eq
-- statement:
--   The Tunnell Map construction uses the b Upper K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L83-L85
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L83-L85

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem TunnellMap.bUpperK_eq {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : bUpperK n F A q = bUpper n F A q := by sorry
