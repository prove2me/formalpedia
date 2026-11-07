-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXMinpoly_monic
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXMinpoly_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:31:19.725195+00:00
-- url     : https://prove2.me/theorems/30e2d9a9-03b3-4fef-90b9-0429701b5b6d
-- title:
--   Cartwright Steger: residue XMinpoly monic
-- statement:
--   The Cartwright Steger construction uses the residue XMinpoly monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L326-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L326-L328

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXMinpoly_monic (P : BasePrime) (r : Rank) (level : Nat) :
    (residueXMinpoly P r level).Monic := by sorry
