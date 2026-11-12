-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_repr_cyclicAlgebra
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_repr_cyclicAlgebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:22:15.220363+00:00
-- url     : https://prove2.me/theorems/aee141ca-843d-4b60-919a-adb00cbdcb02
-- title:
--   Cartwright Steger: building Local Cyclic Basis repr cyclic Algebra
-- statement:
--   Local cyclic coordinates of the represented global cyclic algebra are
--   the images of its function-field cyclic coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean#L310-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean#L310-L362

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLocalCyclicBasis_repr_cyclicAlgebra
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (buildingLocalCyclicBasis P r).repr
        (cyclicAlgebraToBuilding P r x) p =
      functionFieldToBuildingLocalField P
        ((functionFieldCyclicBasis P r).repr x p) := by sorry
