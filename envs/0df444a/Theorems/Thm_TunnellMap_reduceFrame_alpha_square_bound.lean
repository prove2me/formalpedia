-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_alpha_square_bound
-- name    : TunnellMap.reduceFrame_alpha_square_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:51:48.002798+00:00
-- url     : https://prove2.me/theorems/0da8fe2c-d587-56f5-af05-a4f818dadf31
-- title:
--   Tunnell Map: reduce Frame alpha square bound
-- statement:
--   **The reduced-basis size bound applies to the computed frame.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L315-L317
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L315-L317

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_alpha_square_bound (F : OrthogonalFrame p) :
    3 * alpha (reduceFrame F) ^ 2 ≤ 4 * dot p p := by sorry
