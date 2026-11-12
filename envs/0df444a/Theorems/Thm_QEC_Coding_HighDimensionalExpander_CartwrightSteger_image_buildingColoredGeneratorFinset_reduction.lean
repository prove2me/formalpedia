-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_image_buildingColoredGeneratorFinset_reduction
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColoredGeneratorFinset_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:56:52.21719+00:00
-- url     : https://prove2.me/theorems/616baa94-7c9a-4af9-8523-8f10996368f5
-- title:
--   Cartwright Steger: image building Colored Generator Finset reduction
-- statement:
--   The complete finite colored generator set is exactly the congruence
--   image of the complete building colored generator set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L580-L590
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L580-L590

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColoredGeneratorFinset_reduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    (buildingColoredGeneratorFinset P r).image
        (buildingLatticeFiniteReduction P r level) =
      indexColoredGeneratorFinset P r level := by sorry
