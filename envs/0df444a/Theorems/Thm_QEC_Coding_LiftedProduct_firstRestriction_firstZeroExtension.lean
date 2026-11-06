-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
-- name    : QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:53:18.463383+00:00
-- url     : https://prove2.me/theorems/823d5eb2-6b23-45b2-a458-117c6237b752
-- title:
--   Lifted Product: first Restriction first Zero Extension
-- statement:
--   The Lifted Product construction uses the first Restriction first Zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1150-L1155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1150-L1155

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (firstRestriction D).comp (firstZeroExtension D) = LinearMap.id := by sorry
