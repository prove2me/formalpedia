-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2_inr_apply
-- name    : QEC.Coding.HypergraphProduct.boundary2_inr_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:35:23.518618+00:00
-- url     : https://prove2.me/theorems/c6248c85-e1db-486f-b90f-43ea68f01b11
-- title:
--   Hypergraph Product: boundary2 inr apply
-- statement:
--   The Hypergraph Product construction uses the boundary2 inr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L65-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Dimension/BoundaryMaps.lean#L65-L79

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Realization
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
open TensorProduct

theorem QEC.Coding.HypergraphProduct.boundary2_inr_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (x : Word F (C2Index colOne rowTwo)) (r₁ : rowOne) (r₂ : rowTwo) :
    boundary2 D x (Sum.inr (r₁, r₂)) =
      ∑ c₁ : colOne, D.first r₁ c₁ * x (c₁, r₂) := by sorry
