-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:21:56.655907+00:00
-- url     : https://prove2.me/theorems/88303c88-08f4-4ccd-95a5-a8dd34f1d057
-- title:
--   Cartwright Steger: exists building Integer coordinate of cyclic Algebra integral
-- statement:
--   Honest local matrix integrality forces every cyclic coordinate to lie
--   in the building integer ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean#L431-L445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingCyclicCoordinates.lean#L431-L445

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r x)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P
          ((functionFieldCyclicBasis P r).repr x p) := by sorry
