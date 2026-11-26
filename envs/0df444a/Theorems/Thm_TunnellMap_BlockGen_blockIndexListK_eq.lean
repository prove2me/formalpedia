-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_blockIndexListK_eq
-- name    : TunnellMap.BlockGen.blockIndexListK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:36:37.422903+00:00
-- url     : https://prove2.me/theorems/5cbd5b55-da35-563d-83ac-4fbcec1a101e
-- title:
--   Block Gen: block Index List K eq
-- statement:
--   The Block Gen construction uses the block Index List K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L154-L160
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L154-L160

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
open TunnellMap.BlockGen
variable {n : ℤ} {p : Triple}

theorem TunnellMap.BlockGen.blockIndexListK_eq (hn : 0 ≤ n) (F : OrthogonalFrame p) (h : ℤ) :
    blockIndexListK n F h = blockIndexList n F h := by sorry
