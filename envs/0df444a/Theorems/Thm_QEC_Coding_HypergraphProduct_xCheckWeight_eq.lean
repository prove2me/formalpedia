-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_xCheckWeight_eq
-- name    : QEC.Coding.HypergraphProduct.xCheckWeight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:08:51.337754+00:00
-- url     : https://prove2.me/theorems/7ddd29ea-8d27-4dfe-a1af-e557d1d7f52f
-- title:
--   Hypergraph Product: x Check Weight eq
-- statement:
--   Exact weight of an X-check row: a row of `H₁` plus a column of
--   `H₂`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L180-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L180-L221

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.xCheckWeight_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (r₁ : rowOne) (c₂ : colTwo) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (r₁, c₂) 1)) =
      rowWeight D.first r₁ + columnWeight D.second c₂ := by sorry
