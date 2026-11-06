-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_disjoint_hammingSupport_first_second_zeroExtension
-- name    : QEC.Coding.LiftedProduct.disjoint_hammingSupport_first_second_zeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:26.359499+00:00
-- url     : https://prove2.me/theorems/be94c38f-c997-46f1-a76c-9eed3e61c434
-- title:
--   Lifted Product: disjoint hamming Support first second zero Extension
-- statement:
--   The Lifted Product construction uses the disjoint hamming Support first second zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1249-L1266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1249-L1266

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.disjoint_hammingSupport_first_second_zeroExtension
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (aCol × bRow × G))
    (y : Word F (aRow × bCol × G)) :
    Disjoint (hammingSupport (firstZeroExtension D x))
      (hammingSupport (secondZeroExtension D y)) := by sorry
