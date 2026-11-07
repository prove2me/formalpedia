-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionPSL_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionPSL_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:43.120285+00:00
-- url     : https://prove2.me/theorems/9bf40d33-47fb-4bf7-aa94-393f90914663
-- title:
--   Congruence Lifting: residue Transvection PSL injective
-- statement:
--   Distinct residue-field parameters give distinct projective
--   transvections.  The proof rules out their quotient being a scalar matrix by
--   inspecting its fixed off-diagonal entry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L540-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L540-L588

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionPSL_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (residueTransvectionPSL P r level) := by sorry
