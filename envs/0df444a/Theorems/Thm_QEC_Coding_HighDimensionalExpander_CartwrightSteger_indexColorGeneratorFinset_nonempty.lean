-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexColorGeneratorFinset_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColorGeneratorFinset_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:57:25.964704+00:00
-- url     : https://prove2.me/theorems/367cbd4c-3cae-48fd-ad97-efa6223b989d
-- title:
--   Cartwright Steger: index Color Generator Finset nonempty
-- statement:
--   Every prefix color has an actual generator, since it is the image of the
--   nonempty construction-owned apartment-relation set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L495-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L495-L500

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColorGeneratorFinset_nonempty
    (P : BasePrime) (r : Rank) (level k : Nat) :
    (indexColorGeneratorFinset P r level k).Nonempty := by sorry
