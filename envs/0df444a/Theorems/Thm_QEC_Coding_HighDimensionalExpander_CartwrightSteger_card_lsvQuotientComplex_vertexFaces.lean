-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_vertexFaces
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_vertexFaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:40:26.149644+00:00
-- url     : https://prove2.me/theorems/1acddce8-5293-48f2-b5d2-f00fe2a31bd5
-- title:
--   Cartwright Steger: card lsv Quotient Complex vertex Faces
-- statement:
--   Exact zero-dimensional face count of each finite LSV quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1291-L1296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1291-L1296

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_vertexFaces
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) 1) =
      Fintype.card (IndexFiniteGroup P r level) := by sorry
