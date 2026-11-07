-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_traceDual
-- name    : QEC.Coding.f1024SelectedSelfDualBasis_traceDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:57.099072+00:00
-- url     : https://prove2.me/theorems/ca04b64d-7ed9-4c07-bb53-6f47978e5327
-- title:
--   Coding: f1024 Selected Self Dual Basis trace Dual
-- statement:
--   The Coding construction uses the f1024 Selected Self Dual Basis trace Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L529-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L529-L538

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

theorem QEC.Coding.f1024SelectedSelfDualBasis_traceDual :
    f1024SelectedSelfDualBasis.traceDual = f1024SelectedSelfDualBasis := by sorry
