-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_reduced_alpha_le_two_sqrt_div_three
-- name    : TunnellMap.OrderedGenerator.reduced_alpha_le_two_sqrt_div_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:55:09.437649+00:00
-- url     : https://prove2.me/theorems/e5c51945-7e7e-5b1f-b9d5-b7ca3ee389ba
-- title:
--   Ordered Generator: reduced alpha le two sqrt div three
-- statement:
--   The real square-root form stated in the manuscript:
--   `alpha ≤ 2 * sqrt((p·p)/3)`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ReducedBasisBound.lean#L44-L60
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ReducedBasisBound.lean#L44-L60

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_ReducedBasisBound
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {p : Triple}

theorem TunnellMap.OrderedGenerator.reduced_alpha_le_two_sqrt_div_three (F : OrthogonalFrame p)
    (hred : IsLagrangeGaussReduced F) :
    (alpha F : ℝ) ≤ 2 * Real.sqrt ((dot p p : ℝ) / 3) := by sorry
