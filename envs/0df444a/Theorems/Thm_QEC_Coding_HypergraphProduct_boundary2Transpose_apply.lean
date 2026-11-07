-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2Transpose_apply
-- name    : QEC.Coding.HypergraphProduct.boundary2Transpose_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:14:05.447924+00:00
-- url     : https://prove2.me/theorems/f93cdbf3-8500-4bab-93fa-f4b67770d789
-- title:
--   Hypergraph Product: boundary2 Transpose apply
-- statement:
--   Coordinate formula for the transpose of the second HGP boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L228-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L228-L245

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.boundary2Transpose_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (c₁ : colOne) (r₂ : rowTwo) :
    wordLinearMapTranspose (boundary2 D) z (c₁, r₂) =
      (∑ c₂ : colTwo, z (Sum.inl (c₁, c₂)) * D.second r₂ c₂) +
        ∑ r₁ : rowOne, z (Sum.inr (r₁, r₂)) * D.first r₁ c₁ := by sorry
