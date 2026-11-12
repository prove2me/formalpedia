-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_cofaces_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_cofaces_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:59:25.841205+00:00
-- url     : https://prove2.me/theorems/04061696-8c09-44c1-b28e-d59773e35c84
-- title:
--   Cartwright Steger: card lsv Quotient Complex cofaces le
-- statement:
--   Every codimension-one coface count is bounded uniformly in the hierarchy
--   level.  The bound is computed from the constant extension field, not supplied
--   as an assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1587-L1609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1587-L1609

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_cofaces_le
    (P : BasePrime) (r : Rank) (level p : Nat)
    (σ : SimplicialChain.Face (lsvQuotientComplex P r level) p) :
    (SimplicialChain.cofaces (lsvQuotientComplex P r level) p σ).card ≤
      2 * indexColoredGeneratorBound P r := by sorry
