-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_advanceK_eq
-- name    : TunnellMap.BlockGen.advanceK_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:43:41.831801+00:00
-- url     : https://prove2.me/theorems/a5ad3bec-744d-5f9e-bdce-dfd65013eec4
-- title:
--   Block Gen: advance K eq
-- statement:
--   The Block Gen construction uses the advance K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L272-L275
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L272-L275

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
open TunnellMap.BlockGen
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.advanceK_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (st : GenState)
    (h1 : 1 ≤ st.nextBlock) : advanceK s F st = advance s F st := by sorry
