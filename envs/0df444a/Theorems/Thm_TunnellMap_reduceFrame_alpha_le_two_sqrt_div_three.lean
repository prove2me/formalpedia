-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_alpha_le_two_sqrt_div_three
-- name    : TunnellMap.reduceFrame_alpha_le_two_sqrt_div_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:52:34.564374+00:00
-- url     : https://prove2.me/theorems/7a2e4588-2c7b-462e-a00d-b9eefdf8c0d2
-- title:
--   Tunnell Map: reduce Frame alpha le two sqrt div three
-- statement:
--   **The real form of the reduced-basis bound for the computed frame.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L320-L322
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L320-L322

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_alpha_le_two_sqrt_div_three (F : OrthogonalFrame p) :
    (alpha (reduceFrame F) : ℝ) ≤ 2 * Real.sqrt ((dot p p : ℝ) / 3) := by sorry
