-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:07.826205+00:00
-- url     : https://prove2.me/theorems/365bd7a4-7212-4aa5-964e-09cbce6213cc
-- title:
--   Cartwright Steger: cyclic Algebra To Building cyclic Generator Inverse Cyclic Element
-- statement:
--   The Cartwright Steger construction uses the cyclic Algebra To Building cyclic Generator Inverse Cyclic Element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L523-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicAlgebra.lean#L523-L559

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicGeneratorInverseCyclicElement
    (P : BasePrime) (r : Rank) :
    cyclicAlgebraToBuilding P r
        (cyclicGeneratorInverseCyclicElement P r) =
      ((buildingCyclicGeneratorGL P r)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) := by sorry
