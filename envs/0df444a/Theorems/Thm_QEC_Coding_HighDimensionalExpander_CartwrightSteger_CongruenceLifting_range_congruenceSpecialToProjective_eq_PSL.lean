-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_range_congruenceSpecialToProjective_eq_PSL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.range_congruenceSpecialToProjective_eq_PSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:27.150174+00:00
-- url     : https://prove2.me/theorems/fe36278d-f6de-4b7e-99ba-ba4aac5fd654
-- title:
--   Congruence Lifting: range congruence Special To Projective eq PSL
-- statement:
--   Local lifting identifies the full projective special-linear residue image
--   with the reduction of arithmetic special-linear matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L473-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L473-L481

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.range_congruenceSpecialToProjective_eq_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (congruenceSpecialToProjective P r level).range = PSL P r level := by sorry
