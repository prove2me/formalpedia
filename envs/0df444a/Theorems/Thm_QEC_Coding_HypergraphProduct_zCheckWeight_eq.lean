-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_zCheckWeight_eq
-- name    : QEC.Coding.HypergraphProduct.zCheckWeight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:09:20.287197+00:00
-- url     : https://prove2.me/theorems/86a5fe1f-9c5c-4792-b546-24e961bf9fd9
-- title:
--   Hypergraph Product: z Check Weight eq
-- statement:
--   Exact weight of a Z-check row: a row of `H₂` plus a column of
--   `H₁`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L225-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Locality.lean#L225-L256

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.zCheckWeight_eq
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (c₁ : colOne) (r₂ : rowTwo) :
    HammingWeight (boundary2 D (Pi.single (c₁, r₂) 1)) =
      rowWeight D.second r₂ + columnWeight D.first c₁ := by sorry
