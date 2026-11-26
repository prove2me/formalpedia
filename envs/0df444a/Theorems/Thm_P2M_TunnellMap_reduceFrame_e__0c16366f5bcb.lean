-- Prove2me | Theorems.Thm_P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
-- name    : P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:44.917325+00:00
-- url     : https://prove2.me/theorems/ebc37a69-bffd-477f-84a8-13688a3f1b22
-- title:
--   P2 M Tunnell Map reduce Frame e  0c16366f5bcb: P2 M Tunnell Map reduce Frame e  0c16366f5bcb
-- statement:
--   The P2 M Tunnell Map reduce Frame e  0c16366f5bcb construction uses the P2 M Tunnell Map reduce Frame e  0c16366f5bcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L299-L300
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L299-L300

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem P2M_TunnellMap_reduceFrame_e__0c16366f5bcb (F : OrthogonalFrame p) :
    (reduceFrame F).e₁ = (lgReduce F.e₁ F.e₂).1 := by sorry

alias «TunnellMap».«reduceFrame_e₁» := P2M_TunnellMap_reduceFrame_e__0c16366f5bcb

attribute [defeq] P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
