-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_advanceKAux_eq
-- name    : TunnellMap.BlockGen.advanceKAux_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:43:44.029099+00:00
-- url     : https://prove2.me/theorems/d21988d7-1285-5615-962b-90803dcc9621
-- title:
--   Block Gen: advance KAux eq
-- statement:
--   The Block Gen construction uses the advance KAux eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L234-L263
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L234-L263

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

theorem TunnellMap.BlockGen.advanceKAux_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∀ (fuel : ℕ) (st : GenState), 1 ≤ st.nextBlock →
      (hMax n + 1 - st.nextBlock).toNat ≤ fuel →
      advanceKAux s F fuel st = advance s F st := by sorry
