-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_boundary1_canonicalBasisWord_apply
-- name    : QEC.Coding.LiftedProduct.boundary1_canonicalBasisWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:30:07.026286+00:00
-- url     : https://prove2.me/theorems/fe1dab67-cd37-4b69-a107-f3b2c9c33bbe
-- title:
--   Lifted Product: boundary1 canonical Basis Word apply
-- statement:
--   The Lifted Product construction uses the boundary1 canonical Basis Word apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L725-L736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L725-L736

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.boundary1_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (q : QubitIndex aRow aCol bRow bCol G) (c0 : C0Index aRow bRow G) :
    boundary1 D (canonicalBasisWord (F := F) q) c0 = boundary1Matrix D c0 q := by sorry
