-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_bundledIndexGenerator_mul_ne_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_bundledIndexGenerator_mul_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:55:35.294454+00:00
-- url     : https://prove2.me/theorems/868045be-0c2c-4164-abd0-280daa393ccb
-- title:
--   Cartwright Steger: rank Four bundled Index Generator mul ne one
-- statement:
--   A two-step rank-four prefix cannot collapse in the finite quotient: its
--   determinant color is the square of an element of exact order four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L160-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L160-L179

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_bundledIndexGenerator_mul_ne_one
    (P : BasePrime) (level : Nat)
    (u v : ConstantProjectiveClass P .four) :
    bundledIndexGenerator P .four level u *
        bundledIndexGenerator P .four level v ≠ 1 := by sorry
