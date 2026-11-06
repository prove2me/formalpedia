-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_card_qubitIndex
-- name    : QEC.Coding.HypergraphProduct.card_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:47.909602+00:00
-- url     : https://prove2.me/theorems/37a5fa64-dc6b-4d4e-9b16-71ea0d731fe1
-- title:
--   Hypergraph Product: card qubit Index
-- statement:
--   Exact blocklength of the two hypergraph-product qubit blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean#L39-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean#L39-L45

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_HypergraphProduct_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.card_qubitIndex
    {rowOne colOne rowTwo colTwo : Type*}
    [Fintype rowOne] [Fintype colOne] [Fintype rowTwo] [Fintype colTwo] :
    Fintype.card (QubitIndex rowOne colOne rowTwo colTwo) =
      Fintype.card colOne * Fintype.card colTwo +
        Fintype.card rowOne * Fintype.card rowTwo := by sorry
