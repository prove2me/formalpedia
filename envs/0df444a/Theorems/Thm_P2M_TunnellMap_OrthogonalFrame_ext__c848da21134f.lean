-- Prove2me | Theorems.Thm_P2M_TunnellMap_OrthogonalFrame_ext__c848da21134f
-- name    : P2M_TunnellMap_OrthogonalFrame_ext__c848da21134f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:00.201473+00:00
-- url     : https://prove2.me/theorems/2ad4fe0e-84e1-58d3-8d4f-45dd3fd726da
-- title:
--   P2 M Tunnell Map Orthogonal Frame ext  c848da21134f: P2 M Tunnell Map Orthogonal Frame ext  c848da21134f
-- statement:
--   Two orthogonal frames with the same data are equal.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L319-L321
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelGenerator.lean#L319-L321

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
set_option autoImplicit true
open TunnellMap
open OrderedGenerator

theorem P2M_TunnellMap_OrthogonalFrame_ext__c848da21134f {p : Triple} {F G : OrthogonalFrame p}
    (h₁ : F.e₁ = G.e₁) (h₂ : F.e₂ = G.e₂) (h₃ : F.z = G.z) : F = G := by sorry

alias «TunnellMap».«OrthogonalFrame».«ext'» := P2M_TunnellMap_OrthogonalFrame_ext__c848da21134f
