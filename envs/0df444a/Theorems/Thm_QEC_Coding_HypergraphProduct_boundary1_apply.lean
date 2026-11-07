-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1_apply
-- name    : QEC.Coding.HypergraphProduct.boundary1_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:31:20.444187+00:00
-- url     : https://prove2.me/theorems/dbdac0cb-5c55-4e47-af84-d0244572a9d6
-- title:
--   Hypergraph Product: boundary1 apply
-- statement:
--   Coordinate formula for the first hypergraph-product boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L19-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L19-L36

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.boundary1_apply
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (r₁ : rowOne) (c₂ : colTwo) :
    boundary1 D z (r₁, c₂) =
      (∑ c₁ : colOne, D.first r₁ c₁ * z (Sum.inl (c₁, c₂))) +
        ∑ r₂ : rowTwo, (-D.second r₂ c₂) * z (Sum.inr (r₁, r₂)) := by sorry
