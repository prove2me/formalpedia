-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_hammingSupport_sum_blocks
-- name    : QEC.Coding.LiftedProduct.hammingSupport_sum_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:48.755307+00:00
-- url     : https://prove2.me/theorems/9619249f-9591-474f-9e6c-1f5f0b00e15e
-- title:
--   Lifted Product: hamming Support sum blocks
-- statement:
--   The Lifted Product construction uses the hamming Support sum blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1229-L1247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1229-L1247

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.hammingSupport_sum_blocks
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (QubitIndex aRow aCol bRow bCol G)) :
    hammingSupport x =
      (hammingSupport (firstRestriction D x)).map firstEmbedding ∪
        (hammingSupport (secondRestriction D x)).map secondEmbedding := by sorry
