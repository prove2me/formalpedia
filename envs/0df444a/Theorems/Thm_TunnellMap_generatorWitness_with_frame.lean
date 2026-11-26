-- Prove2me | Theorems.Thm_TunnellMap_generatorWitness_with_frame
-- name    : TunnellMap.generatorWitness_with_frame
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:47:48.451424+00:00
-- url     : https://prove2.me/theorems/bece7ae5-54bb-5164-ae46-521d6fdc88b1
-- title:
--   Tunnell Map: generator Witness with frame
-- statement:
--   Every preferred residual edge has affine search data in any oriented
--   frame for the source normal.  Consequently the final generated list is
--   independent of the auxiliary frame.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorRecovery.lean#L75-L143
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/GeneratorRecovery.lean#L75-L143

import Definitions.Def_TunnellMap_MidpointRecord
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_QuadraticRoots
import Definitions.Def_TunnellMap_TauLattice
import Definitions.Def_TunnellMap_GeneratorRecovery
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.generatorWitness_with_frame {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) (R : PreferredMidpointRecord s t)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∃ W : GeneratorWitness s t R, W.frame = F := by sorry
