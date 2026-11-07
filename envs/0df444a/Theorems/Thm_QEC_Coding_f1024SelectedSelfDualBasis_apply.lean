-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_apply
-- name    : QEC.Coding.f1024SelectedSelfDualBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:11:58.164938+00:00
-- url     : https://prove2.me/theorems/fc2972fe-4377-4756-a157-0b9f0e32ae5b
-- title:
--   Coding: f1024 Selected Self Dual Basis apply
-- statement:
--   The Coding construction uses the f1024 Selected Self Dual Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L491-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L491-L502

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

theorem QEC.Coding.f1024SelectedSelfDualBasis_apply (i : Fin 10) :
    f1024SelectedSelfDualBasis i =
      (f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024)) i := by sorry
