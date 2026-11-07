-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_middleHomology_eq_dimension_products
-- name    : QEC.Coding.HypergraphProduct.finrank_middleHomology_eq_dimension_products
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:40:45.665205+00:00
-- url     : https://prove2.me/theorems/6c158fad-d272-4f7f-9542-3453bd119c05
-- title:
--   Hypergraph Product: finrank middle Homology eq dimension products
-- statement:
--   Exact Künneth dimension formula for the general two-input binary
--   Tillich--Zémor hypergraph product.  No input matrix is assumed full rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L196-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/Formula.lean#L196-L248

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.finrank_middleHomology_eq_dimension_products
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (chainComplex D).middleHomology =
      Dimension (firstCode D) * Dimension (secondCode D) +
        Dimension (firstTransposeCode D) *
          Dimension (secondTransposeCode D) := by sorry
