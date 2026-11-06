-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
-- name    : QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:53:53.105374+00:00
-- url     : https://prove2.me/theorems/7aaa4a0e-8c5b-4a26-a85c-ba90e69ae04d
-- title:
--   Lifted Product: second Restriction first Zero Extension
-- statement:
--   The Lifted Product construction uses the second Restriction first Zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1174-L1179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1174-L1179

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (secondRestriction D).comp (firstZeroExtension D) = 0 := by sorry
