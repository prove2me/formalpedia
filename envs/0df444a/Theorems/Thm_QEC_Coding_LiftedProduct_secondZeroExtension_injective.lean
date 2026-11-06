-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_secondZeroExtension_injective
-- name    : QEC.Coding.LiftedProduct.secondZeroExtension_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:31:23.028201+00:00
-- url     : https://prove2.me/theorems/de03a722-a725-4395-8b62-f19cbe252192
-- title:
--   Lifted Product: second Zero Extension injective
-- statement:
--   The Lifted Product construction uses the second Zero Extension injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1189-L1195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1189-L1195

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.secondZeroExtension_injective
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    Function.Injective (secondZeroExtension D) := by sorry
