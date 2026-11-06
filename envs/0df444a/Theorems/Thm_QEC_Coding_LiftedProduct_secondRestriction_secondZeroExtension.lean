-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
-- name    : QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:53:52.361681+00:00
-- url     : https://prove2.me/theorems/08e4e167-a2be-42e1-87a7-de822f6e67e6
-- title:
--   Lifted Product: second Restriction second Zero Extension
-- statement:
--   The Lifted Product construction uses the second Restriction second Zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1158-L1163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1158-L1163

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (secondRestriction D).comp (secondZeroExtension D) = LinearMap.id := by sorry
