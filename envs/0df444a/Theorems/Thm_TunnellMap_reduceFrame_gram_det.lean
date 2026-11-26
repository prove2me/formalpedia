-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_gram_det
-- name    : TunnellMap.reduceFrame_gram_det
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:53:29.078589+00:00
-- url     : https://prove2.me/theorems/395df242-0d31-498e-8b33-e9eb375df49d
-- title:
--   Tunnell Map: reduce Frame gram det
-- statement:
--   The Gram determinant is unchanged by the reduction.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L338-L341
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L338-L341

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_gram_det (F : OrthogonalFrame p) :
    dot (reduceFrame F).e₁ (reduceFrame F).e₁ * dot (reduceFrame F).e₂ (reduceFrame F).e₂ -
        dot (reduceFrame F).e₁ (reduceFrame F).e₂ ^ 2 = dot p p := by sorry
