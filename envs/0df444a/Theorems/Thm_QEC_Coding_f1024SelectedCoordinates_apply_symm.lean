-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_apply_symm
-- name    : QEC.Coding.f1024SelectedCoordinates_apply_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:26:27.093797+00:00
-- url     : https://prove2.me/theorems/89743215-e5c6-46a3-b617-178517763572
-- title:
--   Coding: f1024 Selected Coordinates apply symm
-- statement:
--   The Coding construction uses the f1024 Selected Coordinates apply symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L547-L549
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/SelfDualBasis.lean#L547-L549

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

theorem QEC.Coding.f1024SelectedCoordinates_apply_symm (c : Fin 10 → ZMod 2) :
    f1024SelectedCoordinates (f1024SelectedCoordinates.symm c) = c := by sorry
