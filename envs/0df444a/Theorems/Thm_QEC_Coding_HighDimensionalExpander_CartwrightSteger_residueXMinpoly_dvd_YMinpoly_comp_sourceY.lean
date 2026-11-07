-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXMinpoly_dvd_YMinpoly_comp_sourceY
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXMinpoly_dvd_YMinpoly_comp_sourceY
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:32:13.448194+00:00
-- url     : https://prove2.me/theorems/a1a65058-8e99-423e-8b86-100a98310a71
-- title:
--   Cartwright Steger: residue XMinpoly dvd YMinpoly comp source Y
-- statement:
--   The substitution relation `g(X) ∣ p(y(X))` used by LSV to identify the
--   two residue rings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L340-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueSelection.lean#L340-L352

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXMinpoly_dvd_YMinpoly_comp_sourceY
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueXMinpoly P r level ∣
      (residueYMinpoly P r level).comp (sourceYPolynomial P r) := by sorry
