-- Prove2me | Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dimension
-- name    : QEC.Coding.KT19ReedSolomon.reedSolomonCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:10:57.729074+00:00
-- url     : https://prove2.me/theorems/2e9a6f50-016e-4721-874e-11703423b7c8
-- title:
--   KT19 Reed Solomon: reed Solomon Code dimension
-- statement:
--   The dimension of the actual evaluation code is the number of independent
--   coefficients, whenever its degree bound fits in the field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L132-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean#L132-L136

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators

theorem QEC.Coding.KT19ReedSolomon.reedSolomonCode_dimension (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) : Dimension (reedSolomonCode p l) = l := by sorry
