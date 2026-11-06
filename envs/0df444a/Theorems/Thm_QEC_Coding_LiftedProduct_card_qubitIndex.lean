-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex
-- name    : QEC.Coding.LiftedProduct.card_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:55:49.639175+00:00
-- url     : https://prove2.me/theorems/13d8d76f-b6db-4252-807e-c36f2e590c66
-- title:
--   Lifted Product: card qubit Index
-- statement:
--   The exact number of qubit coordinates in the two lifted-product blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L37-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L37-L50

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.card_qubitIndex
    {aRow aCol bRow bCol G : Type*}
    [Fintype aRow] [Fintype aCol] [Fintype bRow] [Fintype bCol] [Fintype G] :
    Fintype.card (QubitIndex aRow aCol bRow bCol G) =
      Fintype.card G *
        (Fintype.card aCol * Fintype.card bRow +
         Fintype.card aRow * Fintype.card bCol) := by sorry
