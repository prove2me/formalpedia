-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvQuotientComplex_eq_buildingSchreierCliqueComplex
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvQuotientComplex_eq_buildingSchreierCliqueComplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:30:29.971499+00:00
-- url     : https://prove2.me/theorems/38a1fc94-21cf-4216-9424-80a4ce95bdfa
-- title:
--   Cartwright Steger: lsv Quotient Complex eq building Schreier Clique Complex
-- statement:
--   The finite LSV clique complex is exactly the Schreier clique complex of
--   the congruence action of the genuine building lattice.  Consequently the
--   identification covers every clique face, not only vertices or generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L758-L767
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L758-L767

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvQuotientComplex_eq_buildingSchreierCliqueComplex
    (P : BasePrime) (r : Rank) (level : Nat) :
    lsvQuotientComplex P r level =
      CayleyClique.schreierCliqueComplex
        (X := IndexFiniteGroup P r level)
        (buildingColoredGeneratorFinset P r :
          Set (BuildingCartwrightStegerLattice P r)) := by sorry
