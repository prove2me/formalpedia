-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_boundary1Transpose_eq
-- name    : QEC.Coding.HypergraphProduct.finrank_ker_boundary1Transpose_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:36:46.981269+00:00
-- url     : https://prove2.me/theorems/bbbab5b8-545b-4857-a39e-9f2c0829f9e3
-- title:
--   Hypergraph Product: finrank ker boundary1 Transpose eq
-- statement:
--   The first endpoint kernel is the product of the first transpose-code
--   dimension and the second primal-code dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L90-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L90-L120

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.finrank_ker_boundary1Transpose_eq
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) =
      Dimension (firstTransposeCode D) * Dimension (secondCode D) := by sorry
