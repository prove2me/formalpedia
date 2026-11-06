-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
-- name    : QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:53:48.891266+00:00
-- url     : https://prove2.me/theorems/162bdf97-821b-4777-ab9c-bc9b3546df24
-- title:
--   Lifted Product: first Restriction second Zero Extension
-- statement:
--   The Lifted Product construction uses the first Restriction second Zero Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1166-L1171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L1166-L1171

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
    {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (D : Data F G aRow aCol bRow bCol) :
    (firstRestriction D).comp (secondZeroExtension D) = 0 := by sorry
