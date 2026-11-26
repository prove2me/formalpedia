-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_reduced_alpha_square_bound
-- name    : TunnellMap.OrderedGenerator.reduced_alpha_square_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:54:45.591635+00:00
-- url     : https://prove2.me/theorems/cb0b3ebe-a0b1-4e4b-b736-5d9d3caf9c8f
-- title:
--   Ordered Generator: reduced alpha square bound
-- statement:
--   The integral form of the reduced-basis estimate.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ReducedBasisBound.lean#L23-L40
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ReducedBasisBound.lean#L23-L40

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_ReducedBasisBound
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {p : Triple}

theorem TunnellMap.OrderedGenerator.reduced_alpha_square_bound (F : OrthogonalFrame p)
    (hred : IsLagrangeGaussReduced F) :
    3 * alpha F ^ 2 ≤ 4 * dot p p := by sorry
