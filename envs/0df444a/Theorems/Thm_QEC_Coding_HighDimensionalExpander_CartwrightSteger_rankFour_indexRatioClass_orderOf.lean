-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_indexRatioClass_orderOf
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_indexRatioClass_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:55:57.248845+00:00
-- url     : https://prove2.me/theorems/50450595-d2a3-403e-8e0b-74230a580e06
-- title:
--   Cartwright Steger: rank Four index Ratio Class order Of
-- statement:
--   In rank four the selected determinant color has exact order four at
--   every hierarchy level.  The residue degree is a multiple of four and the
--   base prime is odd, so the residue-field unit-group order is divisible by
--   four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L134-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L134-L156

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_indexRatioClass_orderOf
    (P : BasePrime) (level : Nat) :
    orderOf
        (QuotientGroup.mk (indexRatioUnit P .four level) :
          ResiduePowerClass P .four level) = 4 := by sorry
