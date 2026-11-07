-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_qubitDegree_inr_eq
-- name    : QEC.Coding.HypergraphProduct.qubitDegree_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:10:19.395388+00:00
-- url     : https://prove2.me/theorems/da566bd6-2e38-4bdf-8792-93ca06898e50
-- title:
--   Hypergraph Product: qubit Degree inr eq
-- statement:
--   A qubit in `C₁ × C₂` has degree equal to the sum of the two
--   corresponding input row weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L308-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L308-L347

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.qubitDegree_inr_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (r₂ : rowTwo) :
    qubitDegree D (Sum.inr (r₁, r₂)) =
      rowWeight D.second r₂ + rowWeight D.first r₁ := by sorry
