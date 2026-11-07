-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1Transpose_inr_apply
-- name    : QEC.Coding.HypergraphProduct.boundary1Transpose_inr_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:09.466838+00:00
-- url     : https://prove2.me/theorems/44100d78-f1cd-40c8-b40a-ea61d5a23efc
-- title:
--   Hypergraph Product: boundary1 Transpose inr apply
-- statement:
--   The Hypergraph Product construction uses the boundary1 Transpose inr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L34-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L34-L47

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.boundary1Transpose_inr_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C0Index rowOne colTwo)) (r₁ : rowOne) (r₂ : rowTwo) :
    wordLinearMapTranspose (boundary1 D) x (Sum.inr (r₁, r₂)) =
      -∑ c₂ : colTwo, x (r₁, c₂) * D.second r₂ c₂ := by sorry
