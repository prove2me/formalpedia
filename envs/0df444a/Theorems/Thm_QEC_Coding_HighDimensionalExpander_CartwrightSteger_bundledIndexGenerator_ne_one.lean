-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_bundledIndexGenerator_ne_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:41:28.466318+00:00
-- url     : https://prove2.me/theorems/a7689deb-d246-4185-a050-a6ecc4dafbcd
-- title:
--   Cartwright Steger: bundled Index Generator ne one
-- statement:
--   The Cartwright Steger construction uses the bundled Index Generator ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L121-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L121-L128

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_ne_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    bundledIndexGenerator P r level u ≠ 1 := by sorry
