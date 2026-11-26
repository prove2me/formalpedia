-- Prove2me | Theorems.Thm_P2M_TunnellMap_reduceFrame_e__3405bfd3c173
-- name    : P2M_TunnellMap_reduceFrame_e__3405bfd3c173
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:01.213374+00:00
-- url     : https://prove2.me/theorems/da99970a-76a2-4bdd-a1e7-7cb7520c5eef
-- title:
--   P2 M Tunnell Map reduce Frame e  3405bfd3c173: P2 M Tunnell Map reduce Frame e  3405bfd3c173
-- statement:
--   The P2 M Tunnell Map reduce Frame e  3405bfd3c173 construction uses the P2 M Tunnell Map reduce Frame e  3405bfd3c173 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L302-L303
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L302-L303

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem P2M_TunnellMap_reduceFrame_e__3405bfd3c173 (F : OrthogonalFrame p) :
    (reduceFrame F).e₂ = (lgReduce F.e₁ F.e₂).2 := by sorry

alias «TunnellMap».«reduceFrame_e₂» := P2M_TunnellMap_reduceFrame_e__3405bfd3c173

attribute [defeq] P2M_TunnellMap_reduceFrame_e__3405bfd3c173
