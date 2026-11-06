-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_first_dimension_add_rows_eq_cols_add_transpose_dimension
-- name    : QEC.Coding.HypergraphProduct.first_dimension_add_rows_eq_cols_add_transpose_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:53.821547+00:00
-- url     : https://prove2.me/theorems/3b973a28-928e-4321-b6f3-26871eca3e7a
-- title:
--   Hypergraph Product: first dimension add rows eq cols add transpose dimension
-- statement:
--   The source relation `k₁ + r₁ = n₁ + k₁ᵀ`, avoiding truncated
--   subtraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L117-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L117-L133

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.first_dimension_add_rows_eq_cols_add_transpose_dimension
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) :
    Dimension (firstCode D) + Fintype.card rowOne =
      Fintype.card colOne + Dimension (firstTransposeCode D) := by sorry
