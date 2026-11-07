-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYMinpoly_ne_one_add_X
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_ne_one_add_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:32:05.214352+00:00
-- url     : https://prove2.me/theorems/2886737c-0b43-4c23-b4d0-7a867d72b64e
-- title:
--   Cartwright Steger: residue YMinpoly ne one add X
-- statement:
--   The Cartwright Steger construction uses the residue YMinpoly ne one add X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L364-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L364-L375

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Polynomial IntermediateField
open ResidueSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_ne_one_add_X (P : BasePrime) (r : Rank) (level : Nat) :
    residueYMinpoly P r level ≠ 1 + Polynomial.X := by sorry
