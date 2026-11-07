-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:00.933306+00:00
-- url     : https://prove2.me/theorems/01e8fc90-0ccb-4a65-9edc-32951f14ee7b
-- title:
--   Cartwright Steger: cyclic Algebra To Building cartwright Steger Generator Cyclic Element
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra To Building cartwright Steger Generator Cyclic Element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L649-L664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L649-L664

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cartwrightStegerGeneratorCyclicElement
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    cyclicAlgebraToBuilding P r
        (cartwrightStegerGeneratorCyclicElement P r u) =
      (buildingCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u) :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := by sorry
