-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingSchreierGraph_eq_indexCayleyGraph
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingSchreierGraph_eq_indexCayleyGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:56:51.979481+00:00
-- url     : https://prove2.me/theorems/1508cd1b-b8f4-4435-bedb-2dd68d6e9344
-- title:
--   Cartwright Steger: building Schreier Graph eq index Cayley Graph
-- statement:
--   The Schreier graph of the genuine building-lattice action is exactly
--   the finite colored Cayley graph.  This identifies all finite edges with the
--   congruence quotient of the fixed building adjacency relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L619-L661
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L619-L661

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingSchreierGraph_eq_indexCayleyGraph
    (P : BasePrime) (r : Rank) (level : Nat) :
    CayleyClique.schreierGraph
        (X := IndexFiniteGroup P r level)
        (buildingColoredGeneratorFinset P r :
          Set (BuildingCartwrightStegerLattice P r)) =
      SimpleGraph.mulCayley
        (indexColoredGeneratorFinset P r level :
          Set (IndexFiniteGroup P r level)) := by sorry
