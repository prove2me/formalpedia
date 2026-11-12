-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_vertexFaces_eq_buildingQuotient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_vertexFaces_eq_buildingQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:43:24.808283+00:00
-- url     : https://prove2.me/theorems/70eae8e2-7007-49ad-a1aa-e1fbaa1838ae
-- title:
--   Cartwright Steger: card lsv Quotient Complex vertex Faces eq building Quotient
-- statement:
--   Exact zero-face count in terms of the congruence quotient of the
--   simply transitive building lattice itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1313-L1322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1313-L1322

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_vertexFaces_eq_buildingQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) 1) =
      Nat.card
        (BuildingCartwrightStegerLattice P r ⧸
          BuildingCartwrightStegerCongruenceSubgroup P r level) := by sorry
