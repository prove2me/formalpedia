-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYMinpoly_natDegree
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_natDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:31:07.958249+00:00
-- url     : https://prove2.me/theorems/0f3881f9-9e94-4a74-b5f8-8e47038d0fa2
-- title:
--   Cartwright Steger: residue YMinpoly nat Degree
-- statement:
--   The Cartwright Steger construction uses the residue YMinpoly nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L300-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L300-L309

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_natDegree (P : BasePrime) (r : Rank) (level : Nat) :
    (residueYMinpoly P r level).natDegree = r.residueExponent level := by sorry
