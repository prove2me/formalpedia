-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_transpose_boundary2_canonicalBasisWord_apply
-- name    : QEC.Coding.LiftedProduct.transpose_boundary2_canonicalBasisWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:30:34.793166+00:00
-- url     : https://prove2.me/theorems/cd245b35-3df9-40d8-8218-8e483ff151bc
-- title:
--   Lifted Product: transpose boundary2 canonical Basis Word apply
-- statement:
--   The Lifted Product construction uses the transpose boundary2 canonical Basis Word apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L738-L756
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L738-L756

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.transpose_boundary2_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (q : QubitIndex aRow aCol bRow bCol G) (c2 : C2Index aCol bCol G) :
    (wordLinearMapTranspose (boundary2 D)
      (canonicalBasisWord (F := F) q)) c2 = boundary2Matrix D q c2 := by sorry
