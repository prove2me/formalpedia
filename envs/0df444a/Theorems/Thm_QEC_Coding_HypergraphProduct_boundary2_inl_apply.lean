-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2_inl_apply
-- name    : QEC.Coding.HypergraphProduct.boundary2_inl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:31.969978+00:00
-- url     : https://prove2.me/theorems/0dbe6714-7e3a-4717-820d-95d6add0bccb
-- title:
--   Hypergraph Product: boundary2 inl apply
-- statement:
--   The Hypergraph Product construction uses the boundary2 inl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L49-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L49-L63

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.boundary2_inl_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C2Index colOne rowTwo)) (c₁ : colOne) (c₂ : colTwo) :
    boundary2 D x (Sum.inl (c₁, c₂)) =
      ∑ r₂ : rowTwo, D.second r₂ c₂ * x (c₁, r₂) := by sorry
