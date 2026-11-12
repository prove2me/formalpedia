-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_vertexFaces
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_vertexFaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:58:42.311303+00:00
-- url     : https://prove2.me/theorems/e01d7aa5-1468-4b41-b93b-70cf265fdcd3
-- title:
--   Cartwright Steger: card vertex Faces
-- statement:
--   The Cartwright Steger construction uses the card vertex Faces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1227-L1229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1227-L1229

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
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)
omit [DecidableEq V]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_vertexFaces :
    Fintype.card (SimplicialChain.Face K 1) = Fintype.card V := by sorry
