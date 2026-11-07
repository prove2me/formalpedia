-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedSelfDualP_transpose_mul_gram_mul
-- name    : QEC.Coding.f1024SelectedSelfDualP_transpose_mul_gram_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:03.961623+00:00
-- url     : https://prove2.me/theorems/67343f91-20ab-40ec-941d-c3ca382a2159
-- title:
--   Coding: f1024 Selected Self Dual P transpose mul gram mul
-- statement:
--   The Coding construction uses the f1024 Selected Self Dual P transpose mul gram mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L482-L483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L482-L483

import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding

theorem QEC.Coding.f1024SelectedSelfDualP_transpose_mul_gram_mul :
    f1024SelectedSelfDualP.transpose * f1024PolynomialTraceGram * f1024SelectedSelfDualP = 1 := by sorry
