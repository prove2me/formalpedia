-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_hammingSupport_secondZeroExtension
-- name    : QEC.Coding.LiftedProduct.hammingSupport_secondZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:25.96982+00:00
-- url     : https://prove2.me/theorems/2eaee050-5746-4e28-8df3-3ec3738db7a4
-- title:
--   Lifted Product: hamming Support second Zero Extension
-- statement:
--   The Lifted Product construction uses the hamming Support second Zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1213-L1227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1213-L1227

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.hammingSupport_secondZeroExtension
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (x : Word F (aRow × bCol × G)) :
    hammingSupport (secondZeroExtension D x) =
      (hammingSupport x).map secondEmbedding := by sorry
