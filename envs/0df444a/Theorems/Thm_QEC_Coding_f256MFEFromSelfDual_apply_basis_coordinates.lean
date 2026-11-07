-- Prove2me | Theorems.Thm_QEC_Coding_f256MFEFromSelfDual_apply_basis_coordinates
-- name    : QEC.Coding.f256MFEFromSelfDual_apply_basis_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:40.807638+00:00
-- url     : https://prove2.me/theorems/6db10c98-1172-4e3c-b7d9-5368457a81c8
-- title:
--   Coding: f256 MFEFrom Self Dual apply basis coordinates
-- statement:
--   The Coding construction uses the f256 MFEFrom Self Dual apply basis coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/BinaryConversion.lean#L21-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/BinaryConversion.lean#L21-L23

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.f256MFEFromSelfDual_apply_basis_coordinates (x : F256) :
    f256MFEFromSelfDual (f256SelfDualBasis.equivFun x) = f256MFESigma x := by sorry
