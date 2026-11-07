-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1Transpose_inl_apply
-- name    : QEC.Coding.HypergraphProduct.boundary1Transpose_inl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:24.994532+00:00
-- url     : https://prove2.me/theorems/bc677007-90ef-4ba3-a18b-2f9dadcbfbf7
-- title:
--   Hypergraph Product: boundary1 Transpose inl apply
-- statement:
--   The Hypergraph Product construction uses the boundary1 Transpose inl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L19-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L19-L32

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.boundary1Transpose_inl_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C0Index rowOne colTwo)) (c₁ : colOne) (c₂ : colTwo) :
    wordLinearMapTranspose (boundary1 D) x (Sum.inl (c₁, c₂)) =
      ∑ r₁ : rowOne, x (r₁, c₂) * D.first r₁ c₁ := by sorry
