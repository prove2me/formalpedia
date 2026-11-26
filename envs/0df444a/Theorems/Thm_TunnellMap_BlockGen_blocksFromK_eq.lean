-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_blocksFromK_eq
-- name    : TunnellMap.BlockGen.blocksFromK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:17.503157+00:00
-- url     : https://prove2.me/theorems/4427834b-3cb7-5308-acae-d23a96ed95a5
-- title:
--   Block Gen: blocks From K eq
-- statement:
--   The Block Gen construction uses the blocks From K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L205-L221
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L205-L221

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

theorem TunnellMap.BlockGen.blocksFromK_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∀ (fuel : ℕ) (h : ℤ), 1 ≤ h → (hMax n + 1 - h).toNat ≤ fuel →
      blocksFromK s F fuel h = blocksFrom s F h := by sorry
