-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_PSL_unbounded
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.PSL_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:30.441708+00:00
-- url     : https://prove2.me/theorems/e2ee5e85-6726-4a37-bcc0-37082dd5e5e4
-- title:
--   Congruence Lifting: PSL unbounded
-- statement:
--   The selected finite `PSL` endpoints are unbounded along the hierarchy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L612-L616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L612-L616

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.PSL_unbounded (P : BasePrime) (r : Rank) (bound : Nat) :
    ∃ level, bound < Nat.card (PSL P r level) := by sorry
