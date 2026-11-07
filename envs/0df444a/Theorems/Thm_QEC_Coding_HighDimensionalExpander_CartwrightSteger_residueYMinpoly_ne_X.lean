-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYMinpoly_ne_X
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_ne_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:32:09.125657+00:00
-- url     : https://prove2.me/theorems/5503e4cc-94d6-4daf-9a8a-38f23cfc90e1
-- title:
--   Cartwright Steger: residue YMinpoly ne X
-- statement:
--   The selected source prime is distinct from the two inverted, ramified
--   linear factors `y` and `1+y`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L356-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L356-L362

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_ne_X (P : BasePrime) (r : Rank) (level : Nat) :
    residueYMinpoly P r level ≠ Polynomial.X := by sorry
