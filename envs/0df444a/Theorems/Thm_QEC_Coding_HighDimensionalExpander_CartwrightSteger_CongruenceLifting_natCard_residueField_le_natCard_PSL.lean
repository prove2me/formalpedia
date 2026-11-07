-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_natCard_residueField_le_natCard_PSL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.natCard_residueField_le_natCard_PSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:36.007184+00:00
-- url     : https://prove2.me/theorems/57af3709-5bed-4d3c-94ff-48d3ccf11b12
-- title:
--   Congruence Lifting: nat Card residue Field le nat Card PSL
-- statement:
--   The finite projective special-linear group has at least as many elements
--   as its residue field, with no cardinality formula imported as an assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L592-L609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean#L592-L609

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.natCard_residueField_le_natCard_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card (ResidueField P r level) ≤
      Nat.card (PSL P r level) := by sorry
