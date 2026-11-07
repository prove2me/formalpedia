-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYMinpoly_irreducible
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:31:20.616982+00:00
-- url     : https://prove2.me/theorems/7b1493b1-b593-4f9b-85bd-f26f15f24018
-- title:
--   Cartwright Steger: residue YMinpoly irreducible
-- statement:
--   The Cartwright Steger construction uses the residue YMinpoly irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L330-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L330-L332

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_irreducible (P : BasePrime) (r : Rank) (level : Nat) :
    Irreducible (residueYMinpoly P r level) := by sorry
