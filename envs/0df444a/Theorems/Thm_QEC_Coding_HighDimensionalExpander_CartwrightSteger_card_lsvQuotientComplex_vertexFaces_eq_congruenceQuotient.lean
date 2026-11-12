-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_vertexFaces_eq_congruenceQuotient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_vertexFaces_eq_congruenceQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:34:51.233451+00:00
-- url     : https://prove2.me/theorems/730d5446-98db-439c-bfd1-3d5df25e9b2e
-- title:
--   Cartwright Steger: card lsv Quotient Complex vertex Faces eq congruence Quotient
-- statement:
--   Exact zero-face count in terms of the genuine lattice congruence
--   quotient, rather than only its finite image presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1300-L1309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1300-L1309

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_vertexFaces_eq_congruenceQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) 1) =
      Nat.card
        (OrderSplitCartwrightStegerLattice P r ⧸
          OrderSplitCartwrightStegerCongruenceSubgroup P r level) := by sorry
