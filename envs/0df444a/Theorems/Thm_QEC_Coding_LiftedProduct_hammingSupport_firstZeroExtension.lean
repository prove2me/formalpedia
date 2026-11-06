-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_hammingSupport_firstZeroExtension
-- name    : QEC.Coding.LiftedProduct.hammingSupport_firstZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:21.094882+00:00
-- url     : https://prove2.me/theorems/342acacd-e98b-43e2-b05e-4f9a540789fd
-- title:
--   Lifted Product: hamming Support first Zero Extension
-- statement:
--   The Lifted Product construction uses the hamming Support first Zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1197-L1211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1197-L1211

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.hammingSupport_firstZeroExtension
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (aCol × bRow × G)) :
    hammingSupport (firstZeroExtension D x) =
      (hammingSupport x).map firstEmbedding := by sorry
