-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_qubitDegree_inl_eq
-- name    : QEC.Coding.HypergraphProduct.qubitDegree_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:09:00.248689+00:00
-- url     : https://prove2.me/theorems/a09cea0f-5026-4327-8403-cfed2434103a
-- title:
--   Hypergraph Product: qubit Degree inl eq
-- statement:
--   A qubit in `V₁ × V₂` has degree equal to the sum of the two
--   corresponding input column weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L273-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L273-L304

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.qubitDegree_inl_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ : colOne) (c₂ : colTwo) :
    qubitDegree D (Sum.inl (c₁, c₂)) =
      columnWeight D.first c₁ + columnWeight D.second c₂ := by sorry
