-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_symm_apply
-- name    : QEC.Coding.f1024SelectedCoordinates_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:26:23.196108+00:00
-- url     : https://prove2.me/theorems/7565ffdf-d18a-448c-b7c9-a82901e28c24
-- title:
--   Coding: f1024 Selected Coordinates symm apply
-- statement:
--   The Coding construction uses the f1024 Selected Coordinates symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L543-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L543-L545

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

theorem QEC.Coding.f1024SelectedCoordinates_symm_apply (x : F1024) :
    f1024SelectedCoordinates.symm (f1024SelectedCoordinates x) = x := by sorry
